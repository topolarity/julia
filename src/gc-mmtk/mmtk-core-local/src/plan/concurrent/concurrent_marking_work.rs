use crate::plan::concurrent::global::ConcurrentPlan;
use crate::plan::concurrent::Pause;
use crate::plan::tracing::{PlanTrace, Trace};
use crate::plan::PlanTraceObject;
use crate::policy::gc_work::TraceKind;
use crate::scheduler::{GCWork, GCWorker, WorkBucketStage};
use crate::util::{scanning_helper, ObjectReference};
use crate::vm::slot::Slot;
use crate::vm::{Collection, RootsKind, RootsWorkFactory, VMBinding};
use crate::MMTK;

use std::collections::VecDeque;
use std::marker::PhantomData;

pub struct ConcurrentTraceObjects<
    VM: VMBinding,
    P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>,
    const KIND: TraceKind,
> {
    /// initial objects to mark and scan
    initial_objects: Vec<ObjectReference>,
    /// `true` if the `initial_objects` are already marked.
    already_marked: bool,
    phantom_data: PhantomData<(VM, P)>,
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    ConcurrentTraceObjects<VM, P, KIND>
{
    const SATB_BUFFER_SIZE: usize = 8192;
    const CONCURRENT_TRACE_OVERFLOW: usize = Self::SATB_BUFFER_SIZE * 2;
    /// FIX: objects scanned per `do_work` before yielding.  Unbounded packet
    /// execution blocks pause initiation (the all-parked rendezvous) behind an
    /// entire transitive closure; bounding it caps trigger-to-pause latency at
    /// ~a millisecond of marking work.
    const SCAN_BUDGET: usize = 4096;

    pub fn new(initial_objects: Vec<ObjectReference>, already_marked: bool) -> Self {
        Self {
            initial_objects,
            already_marked,
            phantom_data: PhantomData,
        }
    }
}

unsafe impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    Send for ConcurrentTraceObjects<VM, P, KIND>
{
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    GCWork<VM> for ConcurrentTraceObjects<VM, P, KIND>
{
    fn do_work(&mut self, worker: &mut GCWorker<VM>, mmtk: &'static MMTK<VM>) {
        let tls = worker.tls;
        let trace = PlanTrace::<P, KIND>::from_mmtk(mmtk);

        // These are initial objects.  They may not have been marked.
        let initial_objects = std::mem::take(&mut self.initial_objects);
        let num_initial_objects = initial_objects.len();
        let mut num_queued_objects = 0;

        // This queue contains marked but not scanned objects.
        let mut queue = VecDeque::new();
        if self.already_marked {
            // The initial objects are already marked.  Put them in the queue.
            queue.extend(initial_objects);
        } else {
            // We scan each object and only enqueue newly visited objects.
            for object in initial_objects {
                // DIAG/GUARD (env MMTK_TRACE_GUARDS): report and skip garbage
                // entering via roots/modbuf.
                if crate::diag::trace_guards_enabled()
                    && !crate::memory_manager::is_in_mmtk_spaces(object)
                {
                    eprintln!("[trace-garbage] initial={:?}", object);
                    continue;
                }
                trace.trace_object(worker, object, &mut |enqueued_object| {
                    debug_assert_eq!(enqueued_object, object);
                    queue.push_back(enqueued_object);
                    num_queued_objects += 1;
                });
            }
        }

        // Loop until the queue is drained or the scan budget is exhausted.
        let mut scanned = 0usize;
        while let Some(object) = queue.pop_back() {
            // CONTRACT (checked at entry and every 64 objects): while the VM
            // has collections disabled (`jl_gc_disable`), the runtime may
            // hold GC-unobservable heap states -- e.g. package-image objects
            // mid-uniquing whose fields transiently hold encoded values.
            // Scanning must not observe them.  Repackage the remaining
            // (already marked) objects into the Concurrent bucket, which is
            // not polled while collections are disabled; tracing resumes
            // after re-enable.  Marking/enqueuing an object stays safe --
            // only scanning its fields is deferred.
            if scanned % 64 == 0
                && !<VM as VMBinding>::VMCollection::is_collection_enabled()
                && !crate::diag::PAUSE_ACTIVE.load(std::sync::atomic::Ordering::Relaxed)
            {
                queue.push_back(object);
                let rest: Vec<_> = queue.drain(..).collect();
                let w = Self::new(rest, true);
                mmtk.scheduler.work_buckets[WorkBucketStage::Concurrent]
                    .add_boxed_no_notify(Box::new(w));
                break;
            }
            scanned += 1;
            if scanned > Self::SCAN_BUDGET {
                queue.push_back(object);
                let rest: Vec<_> = queue.drain(..).collect();
                let w = Self::new(rest, true);
                worker.add_work(WorkBucketStage::Concurrent, w);
                break;
            }
            scanning_helper::visit_children_non_moving::<VM>(tls, object, &mut |child| {
                // DIAG/GUARD (env MMTK_TRACE_GUARDS): a child outside every
                // MMTk space means the scan of `object` read a non-pointer
                // word as a slot.  Report the parent and its header so the
                // mis-scanned type is identifiable, then skip.
                if crate::diag::trace_guards_enabled()
                    && !crate::memory_manager::is_in_mmtk_spaces(child)
                {
                    let parent_header =
                        unsafe { *((object.to_raw_address().as_usize() - 8) as *const u64) };
                    eprintln!(
                        "[trace-garbage] child={:?} parent={:?} parent_header={:#x}",
                        child, object, parent_header
                    );
                    return child;
                }
                trace.trace_object(worker, child, &mut |enqueued_child| {
                    debug_assert_eq!(enqueued_child, child);
                    queue.push_back(enqueued_child);
                    num_queued_objects += 1;
                })
            });
            trace.post_scan_object(object);

            if queue.len() >= Self::CONCURRENT_TRACE_OVERFLOW {
                let offloaded_objects = queue.drain(..Self::SATB_BUFFER_SIZE).collect();
                let w = Self::new(offloaded_objects, true);
                worker.add_work(WorkBucketStage::Concurrent, w);
            }
        }

        probe!(
            mmtk,
            concurrent_trace_objects,
            num_initial_objects,
            num_queued_objects
        );
    }
}

pub struct ProcessModBufSATB<
    VM: VMBinding,
    P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>,
    const KIND: TraceKind,
> {
    nodes: Option<Vec<ObjectReference>>,
    _p: std::marker::PhantomData<(VM, P)>,
}

unsafe impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    Send for ProcessModBufSATB<VM, P, KIND>
{
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    ProcessModBufSATB<VM, P, KIND>
{
    pub fn new(nodes: Vec<ObjectReference>) -> Self {
        Self {
            nodes: Some(nodes),
            _p: std::marker::PhantomData,
        }
    }
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    GCWork<VM> for ProcessModBufSATB<VM, P, KIND>
{
    fn do_work(&mut self, worker: &mut GCWorker<VM>, mmtk: &'static MMTK<VM>) {
        let mut w = if let Some(nodes) = self.nodes.take() {
            if nodes.is_empty() {
                return;
            }

            ConcurrentTraceObjects::<VM, P, KIND>::new(
                nodes, false, // These objects are not marked, yet.
            )
        } else {
            return;
        };
        GCWork::do_work(&mut w, worker, mmtk);
    }
}

/// A custom implementation of [`RootsWorkFactory`] for concurrent marking.
///
/// Slot roots are loaded immediately and represented as root nodes, just like pinning roots.  All
/// roots are handled by the [`ConcurrentTraceObjects`] work packets.
pub(crate) struct ConcurrentMarkingRootsWorkFactory<
    VM: VMBinding,
    P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>,
    const KIND: TraceKind,
> {
    pub(crate) mmtk: &'static MMTK<VM>,
    phantom_data: PhantomData<P>,
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind> Clone
    for ConcurrentMarkingRootsWorkFactory<VM, P, KIND>
{
    fn clone(&self) -> Self {
        Self {
            mmtk: self.mmtk,
            phantom_data: PhantomData,
        }
    }
}

unsafe impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    Send for ConcurrentMarkingRootsWorkFactory<VM, P, KIND>
{
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    ConcurrentMarkingRootsWorkFactory<VM, P, KIND>
{
    pub(crate) fn new(mmtk: &'static MMTK<VM>) -> Self {
        Self {
            mmtk,
            phantom_data: PhantomData,
        }
    }

    fn debug_assert_initial_mark(&self) {
        let pause = self.mmtk.get_plan().concurrent().unwrap().current_pause();

        debug_assert_eq!(
            pause,
            Some(Pause::InitialMark),
            "Concurrent marking only scans roots during InitialMark."
        );
    }

    fn create_and_schedule_root_nodes_work(&mut self, nodes: Vec<ObjectReference>) {
        let mmtk = self.mmtk;
        let work_packet = ConcurrentTraceObjects::<VM, P, KIND>::new(nodes, false);
        mmtk.scheduler.work_buckets[WorkBucketStage::Concurrent].add_no_notify(work_packet);
    }
}

impl<VM: VMBinding, P: ConcurrentPlan<VM = VM> + PlanTraceObject<VM>, const KIND: TraceKind>
    RootsWorkFactory<VM::VMSlot> for ConcurrentMarkingRootsWorkFactory<VM, P, KIND>
{
    fn create_process_roots_work(&mut self, slots: Vec<VM::VMSlot>) {
        probe!(mmtk, roots, RootsKind::NORMAL, slots.len());

        self.debug_assert_initial_mark();

        // We don't divide the `slots` vector into smaller chunks here.  We assume the VM binding
        // respects the constant `EDGES_WORK_BUFFER_SIZE` and provides lists of slots in reasonable
        // lengths.  Even if a single `ConcurrentTraceObjects` work packet is too large, it can
        // still break up the list during tracing using the constant `CONCURRENT_TRACE_OVERFLOW`.
        let nodes = slots
            .iter()
            .flat_map(|slot| slot.load())
            .collect::<Vec<_>>();

        // Note: During concurrent marking, mutators can overwrite the root slots and make the roots unstable.
        // Therefore, instead of recording the root slots, we record the loaded root nodes.
        #[cfg(feature = "sanity")]
        self.mmtk
            .sanity_checker
            .lock()
            .unwrap()
            .add_root_nodes(nodes.clone());

        self.create_and_schedule_root_nodes_work(nodes);
    }

    fn create_process_pinning_roots_work(&mut self, nodes: Vec<ObjectReference>) {
        probe!(mmtk, roots, RootsKind::PINNING, nodes.len());

        self.debug_assert_initial_mark();

        #[cfg(feature = "sanity")]
        self.mmtk
            .sanity_checker
            .lock()
            .unwrap()
            .add_root_nodes(nodes.clone());

        self.create_and_schedule_root_nodes_work(nodes);
    }

    fn create_process_tpinning_roots_work(&mut self, nodes: Vec<ObjectReference>) {
        probe!(mmtk, roots, RootsKind::TPINNING, nodes.len());

        self.debug_assert_initial_mark();

        #[cfg(feature = "sanity")]
        self.mmtk
            .sanity_checker
            .lock()
            .unwrap()
            .add_root_nodes(nodes.clone());

        self.create_and_schedule_root_nodes_work(nodes);
    }
}
