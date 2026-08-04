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
    /// CONCURRENT FINALIZER SWEEP: queue the deferred sweep packet for the
    /// finalizer entries detached during this (major) pause, and gate lazy
    /// line/block reuse until it completes.  The packet runs post-pause and
    /// the scheduler's all-parked rendezvous guarantees completion before
    /// the next pause, so the mark bits it classifies against stay stable.
    fn finalizer_defer_packet(&self, _w: Box<dyn crate::scheduler::GCWork<Self::VM>>) {
        unimplemented!()
    }
    /// Mark an object reached by the deferred finalizer sweep so reclamation
    /// keeps it (immix: mark bit + line marks; LOS: mark + treadmill move).
    /// Returns `true` if the object was newly marked (its children still
    /// need the same treatment), `false` if it was already live or lives in
    /// a space that is never reclaimed.
    fn finalizer_resurrect_object(&self, _object: crate::util::ObjectReference) -> bool {
        unimplemented!()
    }
    /// Deferred finalizer sweep finished: perform the deferred LOS release
    /// and lift the lazy-reuse gate.
    fn finalizer_sweep_done(&self) {
        unimplemented!()
    }
    /// Whether the current collection was requested explicitly (GC.gc(),
    /// including the exit-path full collections).  Those keep the
    /// synchronous in-pause finalizer sweep: the exit path's
    /// collect-sweep-run loop and prompt-finalization expectations after an
    /// explicit collection both assume to_finalize is populated when the
    /// pause returns.
    fn current_collection_is_user_triggered(&self) -> bool {
        unimplemented!()
    }
}
