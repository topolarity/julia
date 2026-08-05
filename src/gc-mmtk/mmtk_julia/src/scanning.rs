use crate::slots::JuliaVMSlot;
use crate::SINGLETON;
use mmtk::memory_manager;
use mmtk::scheduler::*;
use mmtk::util::opaque_pointer::*;
use mmtk::util::ObjectReference;
use mmtk::vm::slot::Slot;
use mmtk::vm::ObjectTracerContext;
use mmtk::vm::RootsWorkFactory;
use mmtk::vm::Scanning;
use mmtk::vm::SlotVisitor;
use mmtk::vm::VMBinding;
use mmtk::Mutator;
use mmtk::MutatorContext;
use mmtk::MMTK;

use crate::jl_gc_mmtk_sweep_malloced_memory;
use crate::jl_gc_scan_vm_specific_roots;
use crate::jl_gc_sweep_stack_pools_and_mtarraylist_buffers;
#[cfg(feature = "concurrentimmix")]
use crate::julia_types::_jl_task_t;
use crate::JuliaVM;
#[cfg(feature = "concurrentimmix")]
use dashmap::DashMap;
#[cfg(feature = "concurrentimmix")]
use std::sync::{Arc, Mutex};

pub(crate) struct StackRootBuffer {
    pub buffer: Vec<ObjectReference>,
}

impl SlotVisitor<JuliaVMSlot> for StackRootBuffer {
    fn visit_slot(&mut self, slot: JuliaVMSlot) {
        match slot {
            JuliaVMSlot::Simple(se) => {
                if let Some(object) = se.load() {
                    self.buffer.push(object);
                }
            }
            JuliaVMSlot::Offset(oe) => {
                if let Some(object) = oe.load() {
                    self.buffer.push(object);
                }
            }
        }
    }
}

#[cfg(feature = "concurrentimmix")]
lazy_static! {
    pub static ref GC_STACK_SNAPSHOTS: GCStackSnapshots = GCStackSnapshots::new();
}

pub struct VMScanning {}

impl Scanning<JuliaVM> for VMScanning {
    fn scan_roots_in_mutator_thread(
        _tls: VMWorkerThread,
        mutator: &'static mut Mutator<JuliaVM>,
        mut factory: impl RootsWorkFactory<JuliaVMSlot>,
    ) {
        use crate::julia_scanning::*;
        use crate::julia_types::*;
        use mmtk::util::Address;

        let ptls: &mut _jl_tls_states_t = unsafe { std::mem::transmute(mutator.mutator_tls) };
        let mut slot_buffer = StackRootBuffer { buffer: vec![] }; // need to be tpinned as they're all from the shadow stack
        let mut node_buffer = vec![];

        // CONCURRENT STACK SCAN (InitialMark): skip the eager in-pause stack
        // walks.  Every reachable task object is traced during concurrent
        // marking, and the task branch of `scan_julia_object` scans its stack
        // from a per-task snapshot: captured at first resume (the
        // scheduler/safepoint `jl_gc_notify_task_resume` hooks fire before a
        // task can mutate its stack, including the running task at
        // safepoint exit) or lazily at trace time for tasks that stay
        // parked.  InitialMark/FinalMark never move objects, so the
        // transitive pinning this walk provided is not needed; Full GCs
        // (STW tracing, may defrag) keep the eager tpinning walk.  This
        // makes the InitialMark pause O(1) in the number of live tasks
        // instead of ~0.6us per parked task.
        // A/B kill-switch: MMTK_EAGER_STACK_SCAN restores the upstream eager
        // in-pause walk.
        #[cfg(feature = "concurrentimmix")]
        let skip_stack_walk = {
            use std::sync::OnceLock;
            static EAGER: OnceLock<bool> = OnceLock::new();
            !*EAGER.get_or_init(|| std::env::var_os("MMTK_EAGER_STACK_SCAN").is_some())
                && crate::collection::current_pause_is_initial_mark()
        };
        #[cfg(not(feature = "concurrentimmix"))]
        let skip_stack_walk = false;

        // Scan thread local from ptls: See gc_queue_thread_local in gc.c
        let mut root_scan_task = |task: *const _jl_task_t, task_is_root: bool| {
            if !task.is_null() {
                let t0 = mmtk::diag::now_ns();
                if !skip_stack_walk {
                    unsafe {
                        crate::julia_scanning::mmtk_scan_gcstack(task, &mut slot_buffer);
                    }
                } else {
                    // Pre-seed the per-task stack snapshot while the world is
                    // stopped.  This matters for mutators sitting in GC_SAFE
                    // (foreign code) through the whole pause: they never fire
                    // the safepoint-exit `jl_gc_notify_task_resume` hook, so
                    // without a seed the concurrent tracer could capture their
                    // current task's stack while it is running.
                    #[cfg(feature = "concurrentimmix")]
                    crate::scanning::GC_STACK_SNAPSHOTS.resume_barrier_scan_task(task);
                }
                {
                    use std::sync::atomic::Ordering;
                    mmtk::diag::STACKSCAN_NS
                        .fetch_add(mmtk::diag::now_ns().saturating_sub(t0), Ordering::Relaxed);
                    mmtk::diag::STACKSCAN_TASKS.fetch_add(1, Ordering::Relaxed);
                }
                if task_is_root {
                    // captures wrong root nodes before creating the work
                    debug_assert!(
                        Address::from_ptr(task).is_aligned_to(16)
                            || Address::from_ptr(task).is_aligned_to(8),
                        "root node {:?} is not aligned to 8 or 16",
                        Address::from_ptr(task)
                    );

                    // unsafe: We checked `!task.is_null()` before.
                    let objref = unsafe {
                        ObjectReference::from_raw_address_unchecked(Address::from_ptr(task))
                    };
                    node_buffer.push(objref);
                }
            }
        };
        root_scan_task(ptls.root_task, true);

        // need to iterate over live tasks as well to process their shadow stacks
        // we should not set the task themselves as roots as we will know which ones are still alive after GC
        // (skipped entirely for InitialMark: parked tasks' stacks are scanned
        // from snapshots when their task object is traced concurrently)
        if !skip_stack_walk {
            let mut i = 0;
            while i < ptls.gc_tls_common.heap.live_tasks.len {
                let mut task_address = Address::from_ptr(ptls.gc_tls_common.heap.live_tasks.items);
                task_address = task_address.shift::<Address>(i as isize);
                let task = unsafe { task_address.load::<*const jl_task_t>() };
                root_scan_task(task, false);
                i += 1;
            }
        }

        root_scan_task(ptls.current_task as *mut _jl_task_t, true);
        root_scan_task(ptls.next_task, true);
        root_scan_task(ptls.previous_task, true);

        if !ptls.previous_exception.is_null() {
            node_buffer.push(unsafe {
                // unsafe: We have just checked `ptls.previous_exception` is not null.
                ObjectReference::from_raw_address_unchecked(Address::from_mut_ptr(
                    ptls.previous_exception,
                ))
            });
        }

        // Scan backtrace buffer: See gc_queue_bt_buf in gc.c
        let mut i = 0;
        while i < ptls.bt_size {
            unsafe {
                let bt_entry = ptls.bt_data.add(i);
                let bt_entry_size = mmtk_jl_bt_entry_size(bt_entry);
                if mmtk_jl_bt_is_native(bt_entry) {
                    i += bt_entry_size;
                    continue;
                }
                let njlvals = mmtk_jl_bt_num_jlvals(bt_entry);
                for j in 0..njlvals {
                    let bt_entry_value = mmtk_jl_bt_entry_jlvalue(bt_entry, j);

                    // captures wrong root nodes before creating the work
                    debug_assert!(
                        bt_entry_value.to_raw_address().is_aligned_to(16)
                            || bt_entry_value.to_raw_address().is_aligned_to(8),
                        "root node {:?} is not aligned to 8 or 16",
                        bt_entry_value
                    );

                    node_buffer.push(bt_entry_value);
                }
                i += bt_entry_size;
            }
        }

        // We do not need gc_queue_remset from gc.c (we are not using remset in the thread)

        mmtk::diag::STACKSCAN_SLOTS.fetch_add(
            slot_buffer.buffer.len() as u64,
            std::sync::atomic::Ordering::Relaxed,
        );

        // Push work
        const CAPACITY_PER_PACKET: usize = 4096;
        for tpinning_roots in slot_buffer
            .buffer
            .chunks(CAPACITY_PER_PACKET)
            .map(|c| c.to_vec())
        {
            factory.create_process_tpinning_roots_work(tpinning_roots);
        }
        for nodes in node_buffer.chunks(CAPACITY_PER_PACKET).map(|c| c.to_vec()) {
            factory.create_process_pinning_roots_work(nodes);
        }

        // Flush per-mutator barrier/remset buffers before this scan packet is considered done.
        // mmtk-core will be moving this responsibility to the binding (see Task 2 of the plan).
        // For now we double-flush; that's safe because flush is idempotent (drains an empty
        // buffer the second time).
        mutator.flush();
    }

    fn scan_vm_specific_roots(
        _tls: VMWorkerThread,
        mut factory: impl RootsWorkFactory<JuliaVMSlot>,
    ) {
        use crate::slots::RootsWorkClosure;
        let mut roots_closure = RootsWorkClosure::from_roots_work_factory(&mut factory);
        unsafe {
            jl_gc_scan_vm_specific_roots(&mut roots_closure as _);
        }
    }

    fn scan_object<SV: SlotVisitor<JuliaVMSlot>>(
        _tls: VMWorkerThread,
        object: ObjectReference,
        slot_visitor: &mut SV,
    ) {
        process_object(object, slot_visitor);
    }

    fn notify_initial_thread_scan_complete(_partial_scan: bool, _tls: VMWorkerThread) {}

    fn supports_return_barrier() -> bool {
        unimplemented!()
    }

    fn prepare_for_roots_re_scanning() {
        unimplemented!()
    }

    fn process_weak_refs(
        _worker: &mut GCWorker<JuliaVM>,
        tracer_context: impl ObjectTracerContext<JuliaVM>,
    ) -> bool {
        let single_thread_process_finalizer = ScanFinalizersSingleThreaded { tracer_context };
        memory_manager::add_work_packet(
            &SINGLETON,
            WorkBucketStage::VMRefClosure,
            single_thread_process_finalizer,
        );

        // We used to do this in the Compact stage, and add this work packet in notify_initial_thread_scan_complete.
        // But notify_initial_thread_scan_complete is always called, even if MMTK does not do weak reference scanning, which makes it not a good place to add the work packet.
        // I think it makes more sense to do this here -- if MMTK does not do weak ref scanning, this method will not be called and the work packet will not be added.
        let sweep_vm_specific_work = SweepVMSpecific::new();
        memory_manager::add_work_packet(
            &SINGLETON,
            WorkBucketStage::Release, // This has to happen after weak references are processed.
            sweep_vm_specific_work,
        );

        // We have pushed work. No need to repeat this method.
        false
    }
}

pub fn process_object<EV: SlotVisitor<JuliaVMSlot>>(object: ObjectReference, closure: &mut EV) {
    let addr = object.to_raw_address();
    unsafe {
        crate::julia_scanning::scan_julia_object(addr, closure);
    }
}

// Sweep malloced arrays work
pub struct SweepVMSpecific {
    swept: bool,
}

impl SweepVMSpecific {
    pub fn new() -> Self {
        Self { swept: false }
    }
}

impl Default for SweepVMSpecific {
    fn default() -> Self {
        Self::new()
    }
}

impl<VM: VMBinding> GCWork<VM> for SweepVMSpecific {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, _mmtk: &'static MMTK<VM>) {
        // Malloced-memory sweep: when the finalizer phase detached the
        // lists (gate up), the deferred packet sweeps them concurrently;
        // the synchronous path remains for user-triggered collections and
        // non-concurrent plans.
        #[cfg(feature = "concurrentimmix")]
        let deferred = crate::SINGLETON
            .get_plan()
            .concurrent()
            .is_some_and(|p| p.finalizer_sweep_pending());
        #[cfg(not(feature = "concurrentimmix"))]
        let deferred = false;
        if !deferred {
            unsafe { jl_gc_mmtk_sweep_malloced_memory() }
        }
        unsafe { crate::jl_gc_sweep_weak_processing() }
        unsafe { jl_gc_sweep_stack_pools_and_mtarraylist_buffers() }
        self.swept = true;
    }
}

pub struct ScanFinalizersSingleThreaded<C: ObjectTracerContext<JuliaVM>> {
    tracer_context: C,
}

impl<C: ObjectTracerContext<JuliaVM>> GCWork<JuliaVM> for ScanFinalizersSingleThreaded<C> {
    fn do_work(&mut self, worker: &mut GCWorker<JuliaVM>, _mmtk: &'static MMTK<JuliaVM>) {
        self.tracer_context.with_tracer(worker, |tracer| {
            crate::julia_finalizer::scan_finalizers_in_rust(tracer);
        });
    }
}

#[cfg(feature = "concurrentimmix")]
pub struct GCStackSnapshots {
    snapshots: DashMap<usize, Arc<[ObjectReference]>>,
    task_scan_locks: DashMap<usize, Arc<Mutex<()>>>,
    /// Tasks whose stack scan was deferred to the FinalMark pause because a
    /// concurrent capture was not safe at trace time (task running, or GC
    /// disabled so the runtime may hold non-scannable stack states, e.g. a
    /// loader task parked mid-image-restore with unrelocated pointers).
    pending_rescan: DashMap<usize, ()>,
}

#[cfg(feature = "concurrentimmix")]
impl GCStackSnapshots {
    fn new() -> Self {
        Self {
            snapshots: DashMap::new(),
            task_scan_locks: DashMap::new(),
            pending_rescan: DashMap::new(),
        }
    }

    /// Drain the deferred-rescan set.  Called during the FinalMark pause.
    pub fn drain_pending(&self) -> Vec<usize> {
        let keys: Vec<usize> = self.pending_rescan.iter().map(|e| *e.key()).collect();
        for k in &keys {
            self.pending_rescan.remove(k);
        }
        keys
    }

    /// Look up an existing snapshot without capturing one.
    pub fn peek_snapshot(&self, task: *const _jl_task_t) -> Option<Arc<[ObjectReference]>> {
        self.get_snapshot(task)
    }

    fn get_task_scan_lock(&self, task_key: usize) -> Arc<Mutex<()>> {
        self.task_scan_locks
            .entry(task_key)
            .or_insert_with(|| Arc::new(Mutex::new(())))
            .clone()
    }

    fn get_snapshot(&self, task: *const _jl_task_t) -> Option<Arc<[ObjectReference]>> {
        assert!(!task.is_null());

        self.snapshots
            .get(&(task as usize))
            .map(|snapshot| snapshot.clone())
    }

    pub fn gc_thread_scan_stack(&self, task: *const _jl_task_t) -> Option<Arc<[ObjectReference]>> {
        assert!(!task.is_null());

        if let Some(snapshot) = self.get_snapshot(task) {
            return Some(snapshot);
        }

        let task_key = task as usize;
        let task_lock = self.get_task_scan_lock(task_key);
        let _task_lock_guard = task_lock.lock().unwrap();

        if let Some(snapshot) = self.snapshots.get(&task_key) {
            Some(snapshot.clone())
        } else {
            // Capture-at-trace safety, holding the per-task lock (the resume
            // hook serializes on the same lock, so a parked task cannot start
            // running during the walk):
            //  - during a pause the world is stopped: walking is safe (this
            //    matches the exposure of an eager STW root scan);
            //  - otherwise, a running task (`ptls` set) must not be walked,
            //    and while the GC is disabled the runtime may legally hold
            //    non-scannable parked stacks (mid-image-restore yields), so
            //    defer those tasks to the FinalMark pause.
            let in_pause = mmtk::diag::PAUSE_ACTIVE.load(std::sync::atomic::Ordering::Relaxed);
            let running = unsafe { !(*task).ptls.is_null() };
            let disabled = unsafe { crate::jl_get_gc_disable_counter() } > 0;
            if !in_pause && (running || disabled) {
                if std::env::var_os("MMTK_SNAP_TRACE").is_some() {
                    eprintln!(
                        "[snap] DEFER task={:#x} running={} disabled={}",
                        task_key, running, disabled
                    );
                }
                self.pending_rescan.insert(task_key, ());
                return None;
            }
            let snapshot = self.capture_snapshot_who(task, "trace");
            self.snapshots.insert(task_key, snapshot.clone());
            Some(snapshot)
        }
    }

    pub fn resume_barrier_scan_task(&self, task: *const _jl_task_t) {
        assert!(!task.is_null());

        let task_key = task as usize;
        let task_lock = self.get_task_scan_lock(task_key);
        let _task_lock_guard = task_lock.lock().unwrap();
        if self.snapshots.contains_key(&task_key) {
            return;
        }
        let who = if mmtk::diag::PAUSE_ACTIVE.load(std::sync::atomic::Ordering::Relaxed) {
            "preseed"
        } else {
            "hook"
        };
        self.snapshots
            .insert(task_key, self.capture_snapshot_who(task, who));
    }

    fn capture_snapshot(&self, task: *const _jl_task_t) -> Arc<[ObjectReference]> {
        self.capture_snapshot_who(task, "trace")
    }

    fn capture_snapshot_who(&self, task: *const _jl_task_t, who: &str) -> Arc<[ObjectReference]> {
        if std::env::var_os("MMTK_SNAP_TRACE").is_some() {
            eprintln!("[snap] CAPTURE task={:#x} who={}", task as usize, who);
        }
        let mut snapshot_roots = StackRootBuffer { buffer: vec![] };
        unsafe {
            crate::julia_scanning::mmtk_scan_gcstack(task, &mut snapshot_roots);
        }
        // DIAG/GUARD (env MMTK_TRACE_GUARDS): a captured "root" outside every
        // MMTk space is evidence the stack was walked in an unscannable state
        // (torn capture).  Report the capture context and drop the value so
        // the tracer does not chase garbage.
        if mmtk::diag::trace_guards_enabled() {
            let dc = unsafe { crate::jl_get_gc_disable_counter() };
            if dc > 0 {
                eprintln!("[snap-disabled] who={} task={:?} disable={}", who, task, dc);
            }
            let n_before = snapshot_roots.buffer.len();
            snapshot_roots
                .buffer
                .retain(|r| mmtk::memory_manager::is_in_mmtk_spaces(*r));
            let dropped = n_before - snapshot_roots.buffer.len();
            if dropped > 0 {
                let (ptls_null, copy, stkbuf) = unsafe {
                    let ta = &*task;
                    (ta.ptls.is_null(), ta.ctx.copy_stack_custom(), ta.ctx.stkbuf as usize)
                };
                eprintln!(
                    "[snapcheck] who={} task={:?} DROPPED {} of {} refs (ptls_null={} copy_stack={} stkbuf={:#x})",
                    who, task, dropped, n_before, ptls_null, copy, stkbuf
                );
            }
        }
        log::info!(
            "Took snapshot of stack roots for task {:?}, num roots = {}",
            task,
            snapshot_roots.buffer.len()
        );
        Arc::from(snapshot_roots.buffer.into_boxed_slice())
    }

    pub fn clear_snapshots(&self) {
        if std::env::var_os("MMTK_SNAP_TRACE").is_some() {
            eprintln!("[snap] CLEAR n={}", self.snapshots.len());
        }
        self.snapshots.clear();
        self.task_scan_locks.clear();
        self.pending_rescan.clear();
    }
}
