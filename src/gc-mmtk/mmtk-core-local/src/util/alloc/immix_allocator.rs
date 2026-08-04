use std::sync::atomic::Ordering;
use std::sync::Arc;

use super::allocator::{align_allocation_no_fill, fill_alignment_gap, AllocatorContext};
use super::BumpPointer;
use crate::policy::immix::line::*;
use crate::policy::immix::ImmixSpace;
use crate::policy::space::Space;
use crate::util::alloc::allocator::get_maximum_aligned_size;
use crate::util::alloc::Allocator;
use crate::util::linear_scan::Region;
use crate::util::opaque_pointer::VMThread;
use crate::util::rust_util::unlikely;
use crate::util::Address;
use crate::vm::*;

/// Immix allocator
#[repr(C)]
pub struct ImmixAllocator<VM: VMBinding> {
    /// [`VMThread`] associated with this allocator instance
    pub tls: VMThread,
    /// The fastpath bump pointer.
    pub bump_pointer: BumpPointer,
    /// [`Space`](src/policy/space/Space) instance associated with this allocator instance.
    space: &'static ImmixSpace<VM>,
    context: Arc<AllocatorContext<VM>>,
    /// *unused*
    hot: bool,
    /// Is this a copy allocator?
    copy: bool,
    /// Bump pointer for large objects
    pub(in crate::util::alloc) large_bump_pointer: BumpPointer,
    /// Is the current request for large or small?
    request_for_large: bool,
    /// Hole-searching cursor
    line: Option<Line>,
}

/// MMTK_ZERO_MODE=pw: write-intent prefetch of claimed ranges under dirty
/// handover (see `memory::prefetchw_claim`).
fn claim_prefetchw() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("MMTK_ZERO_MODE").map_or(false, |v| v == "pw"))
}

impl<VM: VMBinding> ImmixAllocator<VM> {
    /// FIX E: every acquired block is recorded with the space.  Allocators
    /// reset at every pause, so by the FinalMark that splices these into the
    /// unswept list, no recorded block is still owned.
    fn record_owned(&mut self, block: crate::policy::immix::block::Block) {
        self.immix_space().record_acquired(block);
    }

    pub(crate) fn reset(&mut self) {
        self.bump_pointer.reset(Address::ZERO, Address::ZERO);
        self.large_bump_pointer.reset(Address::ZERO, Address::ZERO);
        self.request_for_large = false;
        self.line = None;
    }
}

impl<VM: VMBinding> Allocator<VM> for ImmixAllocator<VM> {
    fn get_space(&self) -> &'static dyn Space<VM> {
        self.space as _
    }

    fn get_context(&self) -> &AllocatorContext<VM> {
        &self.context
    }

    fn does_thread_local_allocation(&self) -> bool {
        true
    }

    fn get_thread_local_buffer_granularity(&self) -> usize {
        crate::policy::immix::block::Block::BYTES
    }

    fn alloc(&mut self, size: usize, align: usize, offset: usize) -> Address {
        debug_assert!(
            size <= crate::policy::immix::MAX_IMMIX_OBJECT_SIZE,
            "Trying to allocate a {} bytes object, which is larger than MAX_IMMIX_OBJECT_SIZE {}",
            size,
            crate::policy::immix::MAX_IMMIX_OBJECT_SIZE
        );

        let result = align_allocation_no_fill::<VM>(self.bump_pointer.cursor, align, offset);
        let new_cursor = result + size;

        if new_cursor > self.bump_pointer.limit {
            trace!(
                "{:?}: Thread local buffer used up, go to alloc slow path",
                self.tls
            );
            if get_maximum_aligned_size::<VM>(size, align) > Line::BYTES {
                // Size larger than a line: do large allocation
                self.overflow_alloc(size, align, offset)
            } else {
                // Size smaller than a line: fit into holes
                self.alloc_slow_hot(size, align, offset)
            }
        } else {
            // Simple bump allocation.
            fill_alignment_gap::<VM>(self.bump_pointer.cursor, result);
            self.bump_pointer.cursor = new_cursor;
            trace!(
                "{:?}: Bump allocation size: {}, result: {}, new_cursor: {}, limit: {}",
                self.tls,
                size,
                result,
                self.bump_pointer.cursor,
                self.bump_pointer.limit
            );
            result
        }
    }

    /// Acquire a clean block from ImmixSpace for allocation.
    fn alloc_slow_once(&mut self, size: usize, align: usize, offset: usize) -> Address {
        trace!("{:?}: alloc_slow_once", self.tls);
        self.acquire_clean_block(size, align, offset)
    }

    /// This is called when precise stress is used. We try use the thread local buffer for
    /// the allocation (after restoring the correct limit for thread local buffer). If we cannot
    /// allocate from thread local buffer, we will go to the actual slowpath. After allocation,
    /// we will set the fake limit so future allocations will fail the slowpath and get here as well.
    fn alloc_slow_once_precise_stress(
        &mut self,
        size: usize,
        align: usize,
        offset: usize,
        need_poll: bool,
    ) -> Address {
        trace!("{:?}: alloc_slow_once_precise_stress", self.tls);
        // If we are required to make a poll, we call acquire_clean_block() which will acquire memory
        // from the space which includes a GC poll.
        if need_poll {
            trace!(
                "{:?}: alloc_slow_once_precise_stress going to poll",
                self.tls
            );
            let ret = self.acquire_clean_block(size, align, offset);
            // Set fake limits so later allocation will fail in the fastpath, and end up going to this
            // special slowpath.
            self.set_limit_for_stress();
            trace!(
                "{:?}: alloc_slow_once_precise_stress done - forced stress poll",
                self.tls
            );
            return ret;
        }

        // We are not yet required to do a stress GC. We will try to allocate from thread local
        // buffer if possible.  Restore the fake limit to the normal limit so we can do thread
        // local allocation normally. Check if we have exhausted our current thread local block,
        // and if so, then directly acquire a new one
        self.restore_limit_for_stress();
        let ret = if self.require_new_block(size, align, offset) {
            // We don't have enough space in thread local block to service the allocation request,
            // hence allocate a new block
            trace!(
                "{:?}: alloc_slow_once_precise_stress - acquire new block",
                self.tls
            );
            self.acquire_clean_block(size, align, offset)
        } else {
            // This `alloc()` call should always succeed given the if-branch checks if we are out
            // of thread local block space
            trace!("{:?}: alloc_slow_once_precise_stress - alloc()", self.tls,);
            self.alloc(size, align, offset)
        };
        // Set fake limits
        self.set_limit_for_stress();
        ret
    }

    fn get_tls(&self) -> VMThread {
        self.tls
    }
}

impl<VM: VMBinding> ImmixAllocator<VM> {
    pub(crate) fn new(
        tls: VMThread,
        space: Option<&'static dyn Space<VM>>,
        context: Arc<AllocatorContext<VM>>,
        copy: bool,
    ) -> Self {
        ImmixAllocator {
            tls,
            space: space.unwrap().downcast_ref::<ImmixSpace<VM>>().unwrap(),
            context,
            bump_pointer: BumpPointer::default(),
            hot: false,
            copy,
            large_bump_pointer: BumpPointer::default(),
            request_for_large: false,
            line: None,
        }
    }

    pub(crate) fn immix_space(&self) -> &'static ImmixSpace<VM> {
        self.space
    }

    /// Large-object (larger than a line) bump allocation.
    fn overflow_alloc(&mut self, size: usize, align: usize, offset: usize) -> Address {
        trace!("{:?}: overflow_alloc", self.tls);
        let start = align_allocation_no_fill::<VM>(self.large_bump_pointer.cursor, align, offset);
        let end = start + size;
        if end > self.large_bump_pointer.limit {
            self.request_for_large = true;
            let rtn = self.alloc_slow_inline(size, align, offset);
            self.request_for_large = false;
            rtn
        } else {
            fill_alignment_gap::<VM>(self.large_bump_pointer.cursor, start);
            self.large_bump_pointer.cursor = end;
            start
        }
    }

    /// Bump allocate small objects into recyclable lines (i.e. holes).
    fn alloc_slow_hot(&mut self, size: usize, align: usize, offset: usize) -> Address {
        trace!("{:?}: alloc_slow_hot", self.tls);
        if self.acquire_recyclable_lines(size, align, offset) {
            // If stress test is active, then we need to go to the slow path instead of directly
            // calling `alloc()`. This is because the `acquire_recyclable_lines()` function
            // manipulates the cursor and limit if a line can be recycled and if we directly call
            // `alloc()` after recyling a line, then we will miss updating the `allocation_bytes`
            // as the newly recycled line will service the allocation request. If we set the stress
            // factor limit directly in `acquire_recyclable_lines()`, then we risk running into an
            // loop of failing the fastpath (i.e. `alloc()`) and then trying to allocate from a
            // recyclable line.  Hence, we bring the "if we're in stress test" check up a level and
            // directly call `alloc_slow_inline()` which will properly account for the allocation
            // request as well as allocate from the newly recycled line
            let stress_test = self.context.options.is_stress_test_gc_enabled();
            let precise_stress = *self.context.options.precise_stress;
            if unlikely(stress_test && precise_stress) {
                self.alloc_slow_inline(size, align, offset)
            } else {
                self.alloc(size, align, offset)
            }
        } else {
            self.alloc_slow_inline(size, align, offset)
        }
    }

    /// Search for recyclable lines.
    fn acquire_recyclable_lines(&mut self, size: usize, align: usize, offset: usize) -> bool {
        while self.line.is_some() || self.acquire_recyclable_block() {
            let line = self.line.unwrap();
            if let Some((start_line, end_line)) = self.immix_space().get_next_available_lines(line)
            {
                // FIX E: retire validity metadata of the dead objects in this
                // hole before reusing it -- conservative scanning must never
                // see stale VO bits over reallocated memory.
                #[cfg(feature = "vo_bit")]
                crate::util::metadata::vo_bit::bzero_vo_bit(
                    start_line.start(),
                    end_line.start() - start_line.start(),
                );
                #[cfg(feature = "object_pinning")]
                if let crate::util::metadata::MetadataSpec::OnSide(side) =
                    *VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC
                {
                    side.bzero_metadata(start_line.start(), end_line.start() - start_line.start());
                }
                // Find recyclable lines. Update the bump allocation cursor and limit.
                self.bump_pointer.cursor = start_line.start();
                self.bump_pointer.limit = end_line.start();
                trace!(
                    "{:?}: acquire_recyclable_lines -> {:?} [{:?}, {:?}) {:?}",
                    self.tls,
                    self.line,
                    start_line,
                    end_line,
                    self.tls
                );
                // DIRTY HANDOVER: honor the space's zeroed contract (see the
                // plan constructor) instead of unconditionally zeroing the
                // hole -- this memset was a top mutator demand-miss source.
                if self.space.common().zeroed {
                    crate::util::memory::zero_claim(
                        self.bump_pointer.cursor,
                        self.bump_pointer.limit - self.bump_pointer.cursor,
                    );
                } else if claim_prefetchw() {
                    crate::util::memory::prefetchw_claim(
                        self.bump_pointer.cursor,
                        self.bump_pointer.limit - self.bump_pointer.cursor,
                    );
                }
                debug_assert!(
                    align_allocation_no_fill::<VM>(self.bump_pointer.cursor, align, offset) + size
                        <= self.bump_pointer.limit
                );
                let block = line.block();
                self.line = if end_line == block.end_line() {
                    // Hole searching reached the end of a reusable block. Set the hole-searching cursor to None.
                    None
                } else {
                    // Update the hole-searching cursor to None.
                    Some(end_line)
                };
                // LAZY-SWEEP FIX: claimed lines are ALWAYS marked, not only
                // during marking.  Idle-claimed holes were only protected by
                // list membership; marking them closes every line-census
                // double-claim window (triage, hole search, release) at the
                // cost of one cycle of float per claimed hole.
                {
                    let state = self.space.line_mark_state.load(Ordering::Acquire);
                    // LAZY-SWEEP: line epochs are ALWAYS written at claim (triage
                    // liveness).  The object-mark-bit saturation
                    // (allocate-black) is ONLY valid during marking: the
                    // per-cycle clear now runs post-FinalMark, so saturating
                    // outside marking would leave objects "already marked" at
                    // the next InitialMark, making the tracer skip them (and
                    // everything reachable only through them) -- the cause of
                    // the bootstrap typemap corruption.  Outside marking no
                    // mark maintenance is needed: marks always reflect the
                    // last trace (in-pause clear at InitialMark/Full), and a
                    // hole is only offered when its lines went unmarked
                    // through that trace -- no live or stale-marked object
                    // can be inside it.
                    if self.space.should_allocate_as_live() {
                        Line::bulk_set_line_mark_states(state, start_line..end_line);
                        Line::initialize_mark_table_as_marked::<VM>(start_line..end_line);
                    } else {
                        // Idle-window claims use the CLAIMED sentinel so the
                        // nursery census can tell claim noise from survivor
                        // spans (see Line::CLAIMED_MARK_STATE).
                        Line::bulk_set_line_mark_states(
                            Line::CLAIMED_MARK_STATE,
                            start_line..end_line,
                        );
                    }
                    // ALWAYS-ON BARRIER: objects must be born UNARMED.  During
                    // marking, allocate-black covers their liveness and firing
                    // the object-snapshot barrier on a half-initialized object
                    // would enqueue garbage fields; outside marking, an armed
                    // fresh object would look old and flood the remset.  The
                    // claimed range may carry armed bits from dead old
                    // objects; disarm it.
                    if let crate::util::metadata::MetadataSpec::OnSide(unlog) =
                        *VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                    {
                        let start = start_line.start();
                        unlog.bzero_metadata(start, end_line.start() - start);
                    }
                }
                return true;
            } else {
                // No more recyclable lines. Set the hole-searching cursor to None.
                self.line = None;
            }
        }
        false
    }

    /// Get a recyclable block from ImmixSpace.
    fn acquire_recyclable_block(&mut self) -> bool {
        // FIX E: at most ONE chunk of lazy-sweep debt per allocation slow path.
        // An unbounded retry loop would make the first post-GC allocation
        // triage the entire heap (O(heap) mutator stall); bounding it keeps
        // the debt amortized, and all-dead chunks still make progress because
        // their blocks go to the page resource, satisfying the caller's
        // clean-block fallback.
        // CONCURRENT FINALIZER SWEEP: while the gate is up, the reusable
        // pool may contain lines freed by the pause that set it, which the
        // deferred sweep may still resurrect.  Fall through to clean blocks.
        if self
            .immix_space()
            .finalizer_reclaim_gate
            .load(std::sync::atomic::Ordering::SeqCst)
        {
            return false;
        }
        let mut censused = false;
        let mut triaged = false;
        loop {
            match self.immix_space().get_reusable_block(self.copy) {
                Some(block) => {
                    trace!("{:?}: acquire_recyclable_block -> {:?}", self.tls, block);
                    self.record_owned(block);
                    // Set the hole-searching cursor to the start of this block.
                    self.line = Some(block.start_line());
                    return true;
                }
                // Freshest reclaimable memory first: the last minor's blocks
                // (shortest reuse distance), then the aged major backlog.
                _ if !censused => {
                    censused = true;
                    if !self.immix_space().nursery_census_some(32) {
                        continue;
                    }
                }
                _ if !triaged => {
                    triaged = true;
                    // Small quantum (Go-style assist bound): the total sweep
                    // debt is unchanged, but no single allocation pays more
                    // than ~1 MB of triage.
                    if !self.immix_space().lazy_triage_some(32) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
    }

    // Get a clean block from ImmixSpace.
    fn acquire_clean_block(&mut self, size: usize, align: usize, offset: usize) -> Address {
        loop {
        match self.immix_space().get_clean_block(
            self.tls,
            self.copy,
            self.get_context().get_alloc_options(),
        ) {
            // FIX E: before reporting exhaustion, drain lazy-sweep debt --
            // reclaimable memory may still be sitting in the unswept list.
            // Small quantum: the loop retries allocation after every ~4 MB of
            // triage, so the worst single stall stays bounded even here.
            None if self.immix_space().nursery_census_some(128)
                || self.immix_space().lazy_triage_some(128) =>
            {
                continue
            }
            None => return Address::ZERO,
            Some(block) => {
                trace!(
                    "{:?}: Acquired a new block {:?} -> {:?}",
                    self.tls,
                    block.start(),
                    block.end()
                );
                // FIX E: proportional sweep debt (Go-style pacing) -- each
                // block acquisition pays for a few blocks of triage, so the
                // backlog drains steadily instead of concentrating into one
                // stall at the heap-full edge.
                self.immix_space().lazy_triage_some(32);
                // Bulk clear stale line mark state
                self.record_owned(block);
                Line::MARK_TABLE
                    .bzero_metadata(block.start(), crate::policy::immix::block::Block::BYTES);
                // FIX E: clean blocks may be recycled dead blocks whose VO/pin
                // bits were never retired (lazy sweep) -- clear them now.
                #[cfg(feature = "vo_bit")]
                crate::util::metadata::vo_bit::bzero_vo_bit(
                    block.start(),
                    crate::policy::immix::block::Block::BYTES,
                );
                #[cfg(feature = "object_pinning")]
                if let crate::util::metadata::MetadataSpec::OnSide(side) =
                    *VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC
                {
                    side.bzero_metadata(block.start(), crate::policy::immix::block::Block::BYTES);
                }
                // LAZY-SWEEP FIX: see above -- clean blocks are always
                // line-marked at acquisition.
                {
                    let state = self.space.line_mark_state.load(Ordering::Acquire);
                    // See acquire_recyclable_lines: line epochs always;
                    // mark-table saturation while allocate-as-live (marking);
                    // unlog bits always cleared (objects born unarmed).
                    if self.space.should_allocate_as_live() {
                        Line::bulk_set_line_mark_states(
                            state,
                            block.start_line()..block.end_line(),
                        );
                        Line::initialize_mark_table_as_marked::<VM>(
                            block.start_line()..block.end_line(),
                        );
                    } else {
                        // See acquire_recyclable_lines: CLAIMED sentinel.
                        Line::bulk_set_line_mark_states(
                            Line::CLAIMED_MARK_STATE,
                            block.start_line()..block.end_line(),
                        );
                    }
                    if let crate::util::metadata::MetadataSpec::OnSide(unlog) =
                        *VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                    {
                        unlog.bzero_metadata(
                            block.start(),
                            crate::policy::immix::block::Block::BYTES,
                        );
                    }
                }
                if self.request_for_large {
                    self.large_bump_pointer.cursor = block.start();
                    self.large_bump_pointer.limit = block.end();
                } else {
                    self.bump_pointer.cursor = block.start();
                    self.bump_pointer.limit = block.end();
                }
                if !self.space.common().zeroed && claim_prefetchw() {
                    crate::util::memory::prefetchw_claim(
                        block.start(),
                        crate::policy::immix::block::Block::BYTES,
                    );
                }
                return self.alloc(size, align, offset);
            }
        }
        }
    }

    /// Return whether the TLAB has been exhausted and we need to acquire a new block. Assumes that
    /// the buffer limits have been restored using [`ImmixAllocator::restore_limit_for_stress`].
    /// Note that this function may implicitly change the limits of the allocator.
    fn require_new_block(&mut self, size: usize, align: usize, offset: usize) -> bool {
        let result = align_allocation_no_fill::<VM>(self.bump_pointer.cursor, align, offset);
        let new_cursor = result + size;
        let insufficient_space = new_cursor > self.bump_pointer.limit;

        // We want this function to behave as if `alloc()` has been called. Hence, we perform a
        // size check and then return the conditions where `alloc_slow_inline()` would be called
        // in an `alloc()` call, namely when both `overflow_alloc()` and `alloc_slow_hot()` fail
        // to service the allocation request
        if insufficient_space && get_maximum_aligned_size::<VM>(size, align) > Line::BYTES {
            let start =
                align_allocation_no_fill::<VM>(self.large_bump_pointer.cursor, align, offset);
            let end = start + size;
            end > self.large_bump_pointer.limit
        } else {
            // We try to acquire recyclable lines here just like `alloc_slow_hot()`
            insufficient_space && !self.acquire_recyclable_lines(size, align, offset)
        }
    }

    /// Set fake limits for the bump allocation for stress tests. The fake limit is the remaining
    /// thread local buffer size, which should be always smaller than the bump cursor. This method
    /// may be reentrant. We need to check before setting the values.
    fn set_limit_for_stress(&mut self) {
        if self.bump_pointer.cursor < self.bump_pointer.limit {
            let old_limit = self.bump_pointer.limit;
            let new_limit =
                unsafe { Address::from_usize(self.bump_pointer.limit - self.bump_pointer.cursor) };
            self.bump_pointer.limit = new_limit;
            trace!(
                "{:?}: set_limit_for_stress. normal c {} l {} -> {}",
                self.tls,
                self.bump_pointer.cursor,
                old_limit,
                new_limit,
            );
        }

        if self.large_bump_pointer.cursor < self.large_bump_pointer.limit {
            let old_lg_limit = self.large_bump_pointer.limit;
            let new_lg_limit = unsafe {
                Address::from_usize(self.large_bump_pointer.limit - self.large_bump_pointer.cursor)
            };
            self.large_bump_pointer.limit = new_lg_limit;
            trace!(
                "{:?}: set_limit_for_stress. large c {} l {} -> {}",
                self.tls,
                self.large_bump_pointer.cursor,
                old_lg_limit,
                new_lg_limit,
            );
        }
    }

    /// Restore the real limits for the bump allocation so we can properly do a thread local
    /// allocation. The fake limit is the remaining thread local buffer size, and we restore the
    /// actual limit from the size and the cursor. This method may be reentrant. We need to check
    /// before setting the values.
    fn restore_limit_for_stress(&mut self) {
        if self.bump_pointer.limit < self.bump_pointer.cursor {
            let old_limit = self.bump_pointer.limit;
            let new_limit = self.bump_pointer.cursor + self.bump_pointer.limit.as_usize();
            self.bump_pointer.limit = new_limit;
            trace!(
                "{:?}: restore_limit_for_stress. normal c {} l {} -> {}",
                self.tls,
                self.bump_pointer.cursor,
                old_limit,
                new_limit,
            );
        }

        if self.large_bump_pointer.limit < self.large_bump_pointer.cursor {
            let old_lg_limit = self.large_bump_pointer.limit;
            let new_lg_limit =
                self.large_bump_pointer.cursor + self.large_bump_pointer.limit.as_usize();
            self.large_bump_pointer.limit = new_lg_limit;
            trace!(
                "{:?}: restore_limit_for_stress. large c {} l {} -> {}",
                self.tls,
                self.large_bump_pointer.cursor,
                old_lg_limit,
                new_lg_limit,
            );
        }
    }
}
