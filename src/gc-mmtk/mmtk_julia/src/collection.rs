use crate::SINGLETON;
use crate::{
    jl_gc_prepare_to_collect, jl_gc_update_stats, jl_get_gc_disable_counter, jl_hrtime,
    jl_throw_out_of_memory_error,
};
use crate::{JuliaVM, USER_TRIGGERED_GC};
use log::{info, trace};
use mmtk::util::alloc::AllocationError;
use mmtk::util::heap::GCTriggerPolicy;
use mmtk::util::opaque_pointer::*;
use mmtk::vm::{Collection, GCThreadContext};
use mmtk::Mutator;
use std::sync::atomic::{AtomicBool, AtomicIsize, AtomicU64, Ordering};

use crate::{BLOCK_FOR_GC, STW_COND, WORLD_HAS_STOPPED};

pub static GC_START: AtomicU64 = AtomicU64::new(0);

use std::collections::HashSet;
use std::sync::RwLock;
use std::thread::ThreadId;

lazy_static! {
    static ref GC_THREADS: RwLock<HashSet<ThreadId>> = RwLock::new(HashSet::new());
}

#[cfg(feature = "concurrentimmix")]
pub static CONCURRENT_MARKING_ACTIVE: AtomicBool = AtomicBool::new(false);

pub(crate) fn register_gc_thread() {
    let id = std::thread::current().id();
    GC_THREADS.write().unwrap().insert(id);
}
pub(crate) fn unregister_gc_thread() {
    let id = std::thread::current().id();
    GC_THREADS.write().unwrap().remove(&id);
}
pub(crate) fn is_gc_thread() -> bool {
    let id = std::thread::current().id();
    GC_THREADS.read().unwrap().contains(&id)
}

pub struct VMCollection {}

impl Collection<JuliaVM> for VMCollection {
    fn stop_all_mutators<F>(_tls: VMWorkerThread, mut mutator_visitor: F)
    where
        F: FnMut(&'static mut Mutator<JuliaVM>),
    {
        // FIX D: stop the world from the collector side, per the Collection
        // contract ("when the method returns, MMTk assumes the pause starts").
        // Requesting mutators have merely parked in block_for_gc.
        let sw0 = crate::now_ns();
        unsafe { crate::jl_mmtk_gc_stw_begin() };
        crate::record_max(
            &crate::STOP_WAIT_MAX_NS,
            crate::now_ns().saturating_sub(sw0),
        );
        AtomicBool::store(&WORLD_HAS_STOPPED, true, Ordering::SeqCst);

        trace!("Stopped the world!");

        mmtk::diag::PAUSE_PKT_SUM_NS.store(0, Ordering::SeqCst);
        mmtk::diag::PAUSE_PKT_N.store(0, Ordering::SeqCst);
        mmtk::diag::PAUSE_PKT_MAX_NS.store(0, Ordering::SeqCst);
        mmtk::diag::LAST_PKT_END_NS.store(0, Ordering::SeqCst);
        mmtk::diag::TRANS_GAP_SUM_NS.store(0, Ordering::SeqCst);
        mmtk::diag::TRANS_GAP_MAX_NS.store(0, Ordering::SeqCst);
        mmtk::diag::TRANS_N.store(0, Ordering::SeqCst);
        mmtk::diag::CHURN_N.store(0, Ordering::SeqCst);
        mmtk::diag::LAST_SEEN_PKT_N.store(u64::MAX, Ordering::SeqCst);
        mmtk::diag::PAUSE_ACTIVE.store(true, Ordering::SeqCst);
        {
            let now = crate::now_ns();
            crate::STW_START_NS.store(now, Ordering::SeqCst);
            let bs = crate::LAST_BLOCK_START_NS.swap(0, Ordering::SeqCst);
            if bs != 0 {
                let d = now.saturating_sub(bs);
                crate::record_max(&crate::TRIG_MAX_NS, d);
                crate::TRIG_TOTAL_NS.fetch_add(d, Ordering::SeqCst);
                crate::TRIG_COUNT.fetch_add(1, Ordering::SeqCst);
            }
        }
        crate::GC_COUNT_TOTAL.fetch_add(1, Ordering::SeqCst);
        #[cfg(feature = "concurrentimmix")]
        if let Some(cp) = SINGLETON.get_plan().concurrent() {
            if let Some(p) = cp.current_pause() {
                if std::env::var_os("MMTK_PAUSE_TRACE").is_some() {
                    eprintln!("[pause] {:?}", p);
                }
                // `Pause` is public API but lives in a private module, so match on Debug
                match format!("{:?}", p).as_str() {
                    "Full" => { crate::STW_KIND.store(1, Ordering::SeqCst); crate::GC_COUNT_FULL.fetch_add(1, Ordering::SeqCst) },
                    "InitialMark" => { crate::STW_KIND.store(2, Ordering::SeqCst); crate::GC_COUNT_INITIAL.fetch_add(1, Ordering::SeqCst) },
                    "FinalMark" => { crate::STW_KIND.store(3, Ordering::SeqCst); crate::GC_COUNT_FINAL.fetch_add(1, Ordering::SeqCst) },
                    _ => 0,
                };
            }
        }
        if SINGLETON.is_emergency_collection() {
            crate::GC_COUNT_EMERGENCY.fetch_add(1, Ordering::SeqCst);
        }

        // STW -- concurrent marking is not active.
        #[cfg(feature = "concurrentimmix")]
        CONCURRENT_MARKING_ACTIVE.store(false, Ordering::SeqCst);
        crate::MMTK_SATB_MARKING_ACTIVE.store(0, Ordering::SeqCst);

        // Tell MMTk the stacks are ready.
        {
            use mmtk::vm::ActivePlan;
            for mutator in crate::active_plan::VMActivePlan::mutators() {
                info!("stop_all_mutators: visiting {:?}", mutator.mutator_tls);
                mutator_visitor(mutator);
            }
        }

        // Record the start time of the GC
        let now = unsafe { jl_hrtime() };
        trace!("gc_start = {}", now);
        GC_START.store(now, Ordering::Relaxed);
    }

    fn resume_mutators(_tls: VMWorkerThread) {
        // Get the end time of the GC
        let end = unsafe { jl_hrtime() };
        trace!("gc_end = {}", end);
        let gc_time = end - GC_START.load(Ordering::Relaxed);
        unsafe {
            jl_gc_update_stats(
                gc_time,
                crate::api::mmtk_used_bytes(),
                is_current_gc_nursery(),
            )
        }

        // Holding the mutex here guarantees that any mutator that observed
        // `BLOCK_FOR_GC == true` is already enqueued in `wait()` by the time
        // we call `notify_all`.
        let (lock, cvar) = &*STW_COND.clone();
        let count = lock.lock().unwrap();

        #[cfg(feature = "concurrentimmix")]
        {
            // For concurrent Immix, we need to check if SATB is active
            let concurrent_plan = SINGLETON.get_plan().concurrent().unwrap();
            let concurrent_marking_active = concurrent_plan.concurrent_work_in_progress();

            if !concurrent_marking_active {
                crate::scanning::GC_STACK_SNAPSHOTS.clear_snapshots();
            }

            CONCURRENT_MARKING_ACTIVE.store(concurrent_marking_active, Ordering::SeqCst);
            crate::MMTK_SATB_MARKING_ACTIVE
                .store(concurrent_marking_active as u8, Ordering::SeqCst);
            log::info!("Set CONCURRENT_MARKING_ACTIVE to {concurrent_marking_active}");
        }

        {
            let s = crate::STW_START_NS.load(Ordering::SeqCst);
            if s != 0 {
                let d = crate::now_ns().saturating_sub(s);
                crate::record_max(&crate::STW_MAX_NS, d);
                crate::STW_TOTAL_NS.fetch_add(d, Ordering::SeqCst);
                let k = crate::STW_KIND.swap(0, Ordering::SeqCst) as usize;
                crate::STW_KIND_NS[k.min(3)].fetch_add(d, Ordering::SeqCst);
                crate::STW_KIND_N[k.min(3)].fetch_add(1, Ordering::SeqCst);
                if d > crate::STW_KIND_MAX[k.min(3)].load(Ordering::SeqCst) {
                    crate::STW_KIND_MAX[k.min(3)].store(d, Ordering::SeqCst);
                    crate::STW_KIND_MAX_AT[k.min(3)]
                        .store(crate::GC_COUNT_TOTAL.load(Ordering::SeqCst) as u64, Ordering::SeqCst);
                }
                // Pause anatomy: for slow pauses, report whether the time is
                // packet work (sum ~ d x workers) or barrier/idle time.
                if d > 1_500_000 {
                    let fin = mmtk::diag::GC_FINISHED_ENTRY_NS.load(Ordering::SeqCst);
                    let epi = mmtk::diag::now_ns().saturating_sub(fin);
                    eprintln!(
                        "[pause-anatomy] kind={} dur={}us pkt_sum={}us pkt_n={} pkt_max={}us epilogue={}us gaps={}us/{} gap_max={}us",
                        k,
                        d / 1000,
                        mmtk::diag::PAUSE_PKT_SUM_NS.load(Ordering::SeqCst) / 1000,
                        mmtk::diag::PAUSE_PKT_N.load(Ordering::SeqCst),
                        mmtk::diag::PAUSE_PKT_MAX_NS.load(Ordering::SeqCst) / 1000,
                        epi / 1000,
                        mmtk::diag::TRANS_GAP_SUM_NS.load(Ordering::SeqCst) / 1000,
                        mmtk::diag::TRANS_N.load(Ordering::SeqCst),
                        mmtk::diag::TRANS_GAP_MAX_NS.load(Ordering::SeqCst) / 1000
                    );
                    eprintln!(
                        "[pause-churn] churn={} of {} parked-events",
                        mmtk::diag::CHURN_N.load(Ordering::SeqCst),
                        mmtk::diag::TRANS_N.load(Ordering::SeqCst)
                    );
                }
            }
        }
        mmtk::diag::PAUSE_ACTIVE.store(false, Ordering::SeqCst);
        // FIX D: disarm the safepoint before releasing parked requesters.
        unsafe { crate::jl_mmtk_gc_stw_end() };
        AtomicBool::store(&BLOCK_FOR_GC, false, Ordering::SeqCst);
        AtomicBool::store(&WORLD_HAS_STOPPED, false, Ordering::SeqCst);
        cvar.notify_all();
        drop(count);

        info!(
            "Live bytes = {}, total bytes = {}",
            crate::api::mmtk_used_bytes(),
            crate::api::mmtk_total_bytes()
        );

        trace!("Resuming mutators.");
    }

    fn block_for_gc(_tls: VMMutatorThread) {
        info!("Triggered GC!");

        let t0 = crate::now_ns();
        crate::LAST_BLOCK_START_NS.store(t0, Ordering::SeqCst);
        unsafe { jl_gc_prepare_to_collect() };
        let d = crate::now_ns().saturating_sub(t0);
        crate::record_max(&crate::BLOCK_MAX_NS, d);
        crate::BLOCK_TOTAL_NS.fetch_add(d, Ordering::SeqCst);
        crate::BLOCK_COUNT.fetch_add(1, Ordering::SeqCst);

        info!("Finished blocking mutator for GC!");
    }

    fn spawn_gc_thread(_tls: VMThread, ctx: GCThreadContext<JuliaVM>) {
        // Just drop the join handle. The thread will run until the process quits.
        let _ = std::thread::Builder::new()
            .name("MMTk Worker".to_string())
            .spawn(move || {
                use mmtk::util::opaque_pointer::*;
                use mmtk::util::Address;

                // Remember this GC thread
                register_gc_thread();

                // Start the worker loop
                let worker_tls = VMWorkerThread(VMThread(OpaquePointer::from_address(unsafe {
                    Address::from_usize(thread_id::get())
                })));
                match ctx {
                    GCThreadContext::Worker(w) => {
                        mmtk::memory_manager::start_worker(&SINGLETON, worker_tls, w)
                    }
                }

                // The GC thread quits somehow. Unregister this GC thread
                unregister_gc_thread();
            });
    }

    fn schedule_finalization(_tls: VMWorkerThread) {}

    fn out_of_memory(_tls: VMThread, _err_kind: AllocationError) {
        println!("Out of Memory!");
        unsafe { jl_throw_out_of_memory_error() };
    }

    fn vm_live_bytes() -> usize {
        crate::api::JULIA_MALLOC_BYTES.load(Ordering::SeqCst)
    }

    fn is_collection_enabled() -> bool {
        unsafe { jl_get_gc_disable_counter() == 0 }
    }

    fn create_gc_trigger() -> Box<dyn GCTriggerPolicy<JuliaVM>> {
        use crate::gc_trigger::*;
        Box::new(JuliaGCTrigger::new())
    }
}

pub fn is_current_gc_nursery() -> bool {
    match crate::SINGLETON.get_plan().generational() {
        Some(gen) => gen.is_current_gc_nursery(),
        None => false,
    }
}

#[no_mangle]
pub extern "C" fn mmtk_block_thread_for_gc() {
    AtomicBool::store(&BLOCK_FOR_GC, true, Ordering::SeqCst);

    let (lock, cvar) = &*STW_COND.clone();
    let mut count = lock.lock().unwrap();

    info!("Blocking for GC!");

    // FIX D: WORLD_HAS_STOPPED is now set by the GC worker in stop_all_mutators.

    while AtomicBool::load(&BLOCK_FOR_GC, Ordering::SeqCst) {
        count = cvar.wait(count).unwrap();
    }

    AtomicIsize::store(&USER_TRIGGERED_GC, 0, Ordering::SeqCst);
}
