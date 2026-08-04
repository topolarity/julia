use crate::plan::concurrent::concurrent_marking_work::ConcurrentMarkingRootsWorkFactory;
use crate::plan::concurrent::immix::global::ConcurrentImmix;
use crate::plan::generational::gc_work::GenNurseryTrace;
use crate::plan::tracing::PlanTrace;
use crate::policy::gc_work::{TraceKind, DEFAULT_TRACE, TRACE_KIND_TRANSITIVE_PIN};
use crate::policy::immix::TRACE_KIND_FAST;
use crate::vm::VMBinding;

/// The `GCWorkContext` implementation for the fall-back stop-the-world GC in ConcurrentImmix.
pub(super) struct ConcurrentImmixSTWGCWorkContext<VM: VMBinding, const KIND: TraceKind>(
    std::marker::PhantomData<VM>,
);

impl<VM: VMBinding, const KIND: TraceKind> crate::scheduler::GCWorkContext
    for ConcurrentImmixSTWGCWorkContext<VM, KIND>
{
    type VM = VM;
    type PlanType = ConcurrentImmix<VM>;
    type DefaultTrace = PlanTrace<ConcurrentImmix<VM>, KIND>;
    type PinningTrace = PlanTrace<ConcurrentImmix<VM>, TRACE_KIND_TRANSITIVE_PIN>;
}

/// The `GCWorkContext` implementation for the STW nursery (minor) collection:
/// the trace terminates at marked (old) objects via `trace_object_nursery`.
pub(super) struct ConcurrentImmixNurseryGCWorkContext<VM: VMBinding>(std::marker::PhantomData<VM>);

impl<VM: VMBinding> crate::scheduler::GCWorkContext for ConcurrentImmixNurseryGCWorkContext<VM> {
    type VM = VM;
    type PlanType = ConcurrentImmix<VM>;
    type DefaultTrace = GenNurseryTrace<VM, Self::PlanType, DEFAULT_TRACE>;
    type PinningTrace = GenNurseryTrace<VM, Self::PlanType, TRACE_KIND_TRANSITIVE_PIN>;
}

/// The `GCWorkContext` implementation for concurrent marking.  Note that it overrides the
/// `RootsWorkFactory`.
pub(super) struct ConcurrentImmixGCWorkContext<VM>(std::marker::PhantomData<VM>);

impl<VM: VMBinding> crate::scheduler::GCWorkContext for ConcurrentImmixGCWorkContext<VM> {
    type VM = VM;
    type PlanType = ConcurrentImmix<VM>;
    type DefaultTrace = PlanTrace<Self::PlanType, TRACE_KIND_FAST>;
    type PinningTrace = PlanTrace<Self::PlanType, TRACE_KIND_FAST>;

    fn make_roots_work_factory(
        mmtk: &'static crate::MMTK<Self::VM>,
    ) -> impl crate::vm::RootsWorkFactory<<Self::VM as VMBinding>::VMSlot> {
        ConcurrentMarkingRootsWorkFactory::<Self::VM, Self::PlanType, TRACE_KIND_FAST>::new(mmtk)
    }
}
