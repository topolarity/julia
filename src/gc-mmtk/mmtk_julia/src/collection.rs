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

/// True while the world is stopped for an InitialMark pause.  Used by the
/// mutator root scan to decide between eager in-pause stack walking (Full:
/// STW tracing, may defrag, needs the tpinning walk) and deferred
/// snapshot-based stack scanning during concurrent marking (InitialMark).
#[cfg(feature = "concurrentimmix")]
pub(crate) fn current_pause_is_initial_mark() -> bool {
    if let Some(cp) = SINGLETON.get_plan().concurrent() {
        if let Some(p) = cp.current_pause() {
            // `Pause` is public API but lives in a private module, so match on Debug
            return format!("{:?}", p) == "InitialMark";
        }
    }
    false
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
        for s in [
            &mmtk::diag::ROOTS_MUT_NS,
            &mmtk::diag::ROOTS_MUT_MAX_NS,
            &mmtk::diag::ROOTS_MUT_N,
            &mmtk::diag::ROOTS_VM_NS,
            &mmtk::diag::PREP_NS,
            &mmtk::diag::PREP_MUT_NS,
            &mmtk::diag::PREP_IMM_NS,
            &mmtk::diag::PREP_LOS_NS,
            &mmtk::diag::PREP_NM_NS,
            &mmtk::diag::PREP_BASE_NS,
            &mmtk::diag::STACKSCAN_NS,
            &mmtk::diag::STACKSCAN_TASKS,
            &mmtk::diag::STACKSCAN_SLOTS,
        ] {
            s.store(0, Ordering::SeqCst);
        }
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
                    "Nursery" => { crate::STW_KIND.store(4, Ordering::SeqCst); crate::GC_COUNT_NURSERY.fetch_add(1, Ordering::SeqCst) },
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
        crate::set_satb_marking_active(false);
        mmtk::diag::SATB_MARKING_ACTIVE.store(false, Ordering::SeqCst);

        // FinalMark: trace the stacks of tasks whose concurrent snapshot
        // capture was deferred (task was running, or GC was disabled).  The
        // world is now stopped, so their stacks are frozen.  Prefer the
        // first-resume snapshot when one was captured since (it is the
        // Init-state, strictly more conservative); the values are traced with
        // SATB-snapshot semantics in the Closure stage, ahead of the
        // weak-ref/finalizer stages that read mark bits.
        #[cfg(feature = "concurrentimmix")]
        if crate::STW_KIND.load(Ordering::SeqCst) == 3 {
            let pending = crate::scanning::GC_STACK_SNAPSHOTS.drain_pending();
            if !pending.is_empty() {
                let mut values: Vec<mmtk::util::ObjectReference> = vec![];
                for key in &pending {
                    let task = *key as *const crate::julia_types::_jl_task_t;
                    if let Some(snapshot) =
                        crate::scanning::GC_STACK_SNAPSHOTS.peek_snapshot(task)
                    {
                        values.extend(snapshot.iter().copied());
                    } else {
                        let mut buf = crate::scanning::StackRootBuffer { buffer: vec![] };
                        unsafe {
                            crate::julia_scanning::mmtk_scan_gcstack(task, &mut buf);
                        }
                        values.extend(buf.buffer);
                    }
                }
                if mmtk::diag::trace_guards_enabled()
                    || std::env::var_os("MMTK_ROOT_ANATOMY").is_some()
                {
                    eprintln!(
                        "[pending-rescan] finalmark: {} tasks, {} stack values",
                        pending.len(),
                        values.len()
                    );
                }
                SINGLETON
                    .get_plan()
                    .concurrent()
                    .unwrap()
                    .enqueue_satb_values(values);
            }
        }

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
            crate::set_satb_marking_active(concurrent_marking_active);
            mmtk::diag::SATB_MARKING_ACTIVE.store(concurrent_marking_active, Ordering::SeqCst);
            log::info!("Set CONCURRENT_MARKING_ACTIVE to {concurrent_marking_active}");
        }

        {
            let s = crate::STW_START_NS.load(Ordering::SeqCst);
            if s != 0 {
                let d = crate::now_ns().saturating_sub(s);
                crate::record_max(&crate::STW_MAX_NS, d);
                crate::STW_TOTAL_NS.fetch_add(d, Ordering::SeqCst);
                let k = crate::STW_KIND.swap(0, Ordering::SeqCst) as usize;
                crate::STW_KIND_NS[k.min(4)].fetch_add(d, Ordering::SeqCst);
                crate::STW_KIND_N[k.min(4)].fetch_add(1, Ordering::SeqCst);
                if d > crate::STW_KIND_MAX[k.min(4)].load(Ordering::SeqCst) {
                    crate::STW_KIND_MAX[k.min(4)].store(d, Ordering::SeqCst);
                    crate::STW_KIND_MAX_AT[k.min(4)]
                        .store(crate::GC_COUNT_TOTAL.load(Ordering::SeqCst) as u64, Ordering::SeqCst);
                }
                // Per-pause packet-type histogram (MMTK_PAUSE_PKT_HIST).
                if mmtk::diag::pkt_hist_enabled() {
                    mmtk::diag::pkt_hist_dump();
                }
                // Root-scan anatomy: per-pause breakdown of the in-pause root
                // work by class (env-gated; used to size the Init floor).
                {
                    use std::sync::OnceLock;
                    static ROOT_ANATOMY: OnceLock<bool> = OnceLock::new();
                    if *ROOT_ANATOMY
                        .get_or_init(|| std::env::var_os("MMTK_ROOT_ANATOMY").is_some())
                    {
                        let us = |v: u64| v as f64 / 1000.0;
                        eprintln!(
                            "[roots] kind={} dur={:.1}us mut={:.1}us(max {:.1}us, n={}) stack={:.1}us(tasks={} slots={}) vm={:.1}us prep={:.1}us prepmut={:.1}us prep[imm={:.1} los={:.1} nm={:.1} base={:.1}]us pkt_sum={:.1}us pkt_n={}",
                            k,
                            us(d),
                            us(mmtk::diag::ROOTS_MUT_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::ROOTS_MUT_MAX_NS.load(Ordering::SeqCst)),
                            mmtk::diag::ROOTS_MUT_N.load(Ordering::SeqCst),
                            us(mmtk::diag::STACKSCAN_NS.load(Ordering::SeqCst)),
                            mmtk::diag::STACKSCAN_TASKS.load(Ordering::SeqCst),
                            mmtk::diag::STACKSCAN_SLOTS.load(Ordering::SeqCst),
                            us(mmtk::diag::ROOTS_VM_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_MUT_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_IMM_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_LOS_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_NM_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PREP_BASE_NS.load(Ordering::SeqCst)),
                            us(mmtk::diag::PAUSE_PKT_SUM_NS.load(Ordering::SeqCst)),
                            mmtk::diag::PAUSE_PKT_N.load(Ordering::SeqCst),
                        );
                    }
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
