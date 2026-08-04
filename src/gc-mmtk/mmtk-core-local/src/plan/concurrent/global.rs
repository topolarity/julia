use crate::plan::concurrent::Pause;
use crate::plan::Plan;

/// Trait for a concurrent plan.
pub trait ConcurrentPlan: Plan {
    /// Return `true`` if concurrent work (such as concurrent marking) is in progress.
    fn concurrent_work_in_progress(&self) -> bool;
    /// Return the current pause kind.  `None` if not in a pause.
    fn current_pause(&self) -> Option<Pause>;
    /// Enqueue a batch of object values to be traced with SATB-snapshot
    /// semantics (same treatment as barrier-logged old values).  Used by the
    /// binding during the FinalMark pause to trace stack values of tasks
    /// whose concurrent snapshot capture was deferred.
    fn enqueue_satb_values(&self, _values: Vec<crate::util::ObjectReference>) {
        unimplemented!()
    }
    /// A live-set estimate in pages for heap-target sizing.  Under lazy
    /// sweeping, `get_reserved_pages` includes dead-but-untriaged backlog,
    /// so a trigger policy that bases its target on reserved pages inflates
    /// it unboundedly; this estimate excludes the backlog.
    fn live_pages_estimate(&self) -> Option<usize> {
        None
    }
    /// ALWAYS-ON BARRIER: accept a flushed batch of remembered-set entries
    /// (old objects mutated outside marking) from a mutator's barrier.
    fn append_remset(&self, _buf: Vec<crate::util::ObjectReference>) {
        unimplemented!()
    }
}
