use super::defrag::StatsForDefrag;
use super::line::*;
use super::{block::*, defrag::Defrag};
use crate::plan::tracing::OptionObjectQueue;
use crate::policy::gc_work::{TraceKind, DEFAULT_TRACE, TRACE_KIND_TRANSITIVE_PIN};
use crate::policy::sft::GCWorkerMutRef;
use crate::policy::sft::SFT;
use crate::policy::sft_map::SFTMap;
use crate::policy::space::{CommonSpace, Space};
use crate::util::alloc::allocator::AllocationOptions;
use crate::util::alloc::allocator::AllocatorContext;
use crate::util::constants::LOG_BYTES_IN_PAGE;
use crate::util::heap::chunk_map::*;
use crate::util::heap::BlockPageResource;
use crate::util::heap::PageResource;
use crate::util::linear_scan::{Region, RegionIterator};
use crate::util::metadata::log_bit::UnlogBitsOperation;
use crate::util::metadata::side_metadata::SideMetadataSpec;
#[cfg(feature = "vo_bit")]
use crate::util::metadata::vo_bit;
use crate::util::metadata::{self, MetadataSpec};
use crate::util::object_enum::ObjectEnumerator;
use crate::util::object_forwarding;
use crate::util::{copy::*, epilogue, object_enum};
use crate::util::{Address, ObjectReference};
use crate::vm::*;
use crate::{
    plan::ObjectQueue,
    scheduler::{GCWork, GCWorkScheduler, GCWorker, WorkBucketStage},
    util::opaque_pointer::{VMThread, VMWorkerThread},
    MMTK,
};
use atomic::Ordering;
use std::sync::{atomic::AtomicU8, atomic::AtomicUsize, Arc};

pub(crate) const TRACE_KIND_FAST: TraceKind = 0;
pub(crate) const TRACE_KIND_DEFRAG: TraceKind = 1;

/// Shared live-bytes total for the (single) immix space, fed by per-worker
/// thread-local cells flushed at packet boundaries.
pub static LIVE_BYTES_TOTAL: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
thread_local! {
    static LIVE_BYTES_TLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// Flush the executing thread's live-bytes cell into the shared total.
/// Called from the worker loop after each work packet.
pub fn flush_live_bytes_tls() {
    LIVE_BYTES_TLS.with(|c| {
        let v = c.take();
        if v != 0 {
            LIVE_BYTES_TOTAL.fetch_add(v, std::sync::atomic::Ordering::Relaxed);
        }
    });
}

pub struct ImmixSpace<VM: VMBinding> {
    common: CommonSpace<VM>,
    pr: BlockPageResource<VM, Block>,
    /// Allocation status for all chunks in immix space
    pub chunk_map: ChunkMap,
    /// Current line mark state
    pub line_mark_state: AtomicU8,
    /// Line mark state in previous GC
    line_unavail_state: AtomicU8,
    /// A list of all reusable blocks
    pub reusable_blocks: ReusableBlockPool,
    /// Defrag utilities
    pub(super) defrag: Defrag,
    /// How many lines have been consumed since last GC?
    lines_consumed: AtomicUsize,
    /// FIX E (lazy sweep): blocks awaiting triage.  Single-membership
    /// invariant: every allocated block is in exactly one of {unswept, the
    /// reusable pool, an allocator's owned list, pending, full_blocks, or
    /// free}.  `pending` collects blocks abandoned by allocator resets and is
    /// spliced into `unswept` only at FinalMark, so everything in `unswept`
    /// has survived a full marking and is safe to triage at any time.
    unswept_blocks: std::sync::Mutex<Vec<Block>>,
    /// PATH 2: blocks listed at the LAST FinalMark.  Their garbage is still
    /// epoch-marked (SATB float): neither reclaimable nor worth triaging until
    /// the next FinalMark ages them into `unswept_blocks`.
    unswept_young: std::sync::Mutex<Vec<Block>>,
    /// LEG 1 (fewer in-pause work items): packets generated at FinalMark that
    /// only need to complete before the NEXT pause (unlog-bit clearing,
    /// mark-bit clearing).  Drained into the always-open bucket by the plan's
    /// `end_of_gc`, so they execute concurrently after mutators resume.  The
    /// all-parked rendezvous guarantees they finish before the next pause is
    /// scheduled.
    deferred_post_pause_packets: std::sync::Mutex<Vec<Box<dyn GCWork<VM>>>>,
    /// PATH 2: bytes of objects marked this cycle (Go's `heapMarked`).
    live_bytes: &'static std::sync::atomic::AtomicUsize,
    /// CONCURRENT FINALIZER SWEEP: while set, lazy triage must not hand out
    /// lines freed by the pause that set it -- the deferred finalizer sweep
    /// still reads (and may resurrect) dead objects in them.
    pub(crate) finalizer_reclaim_gate: std::sync::atomic::AtomicBool,
    /// Snapshot of `live_bytes` at the last FinalMark.
    live_bytes_prev: std::sync::atomic::AtomicUsize,
    pending_blocks: std::sync::Mutex<Vec<Block>>,
    /// Lock-free mirror of `unswept_blocks.is_empty()`.  The triage entry
    /// runs on every allocator refill; between majors the backlog is empty
    /// and the wrapper's diag clocks alone cost ~36ms/pass (measured) --
    /// exit before touching clocks or locks.  Written only inside pauses
    /// (aging) and by the triage that empties the list, so a stale value
    /// can only cause one extra timed call, never skipped work.
    unswept_nonempty: std::sync::atomic::AtomicBool,
    /// LAZY NURSERY CENSUS: blocks drained from `pending_blocks` at a minor
    /// pause, awaiting claim-time classification.  The census does not need
    /// the world stopped (object marks are stable between collections), so
    /// the pause pays only an O(1) splice; classification runs on the
    /// allocator slow path like the majors' lazy triage.
    unswept_nursery: std::sync::Mutex<Vec<Block>>,
    nursery_unswept_nonempty: std::sync::atomic::AtomicBool,
    /// NURSERY ACCOUNTING: free lines handed to allocators since the last
    /// collection.  This is the real nursery size for the minor trigger:
    /// counting whole pending blocks over-fires ~3x, because a pool re-pop
    /// of a holed block counts 32KB while offering only its free lines.
    nursery_lines_claimed: std::sync::atomic::AtomicUsize,
    full_blocks: std::sync::Mutex<Vec<Block>>,
    /// Object mark state
    mark_state: u8,
    /// Work packet scheduler
    scheduler: Arc<GCWorkScheduler<VM>>,
    /// Some settings for this space
    space_args: ImmixSpaceArgs,
}

/// Some arguments for Immix Space.
pub struct ImmixSpaceArgs {
    /// Whether this ImmixSpace instance contains both young and old objects.
    /// This affects the updating of valid-object bits.  If some lines or blocks of this ImmixSpace
    /// instance contain young objects, their VO bits need to be updated during this GC.  Currently
    /// only StickyImmix is affected.  GenImmix allocates young objects in a separete CopySpace
    /// nursery and its VO bits can be cleared in bulk.
    pub mixed_age: bool,
    /// Disable copying for this Immix space.
    pub never_move_objects: bool,
}

unsafe impl<VM: VMBinding> Sync for ImmixSpace<VM> {}

impl<VM: VMBinding> SFT for ImmixSpace<VM> {
    fn name(&self) -> &'static str {
        self.get_name()
    }

    fn get_forwarded_object(&self, object: ObjectReference) -> Option<ObjectReference> {
        // If we never move objects, look no further.
        if !self.is_movable() {
            return None;
        }

        if object_forwarding::is_forwarded::<VM>(object) {
            Some(object_forwarding::read_forwarding_pointer::<VM>(object))
        } else {
            None
        }
    }

    fn is_live(&self, object: ObjectReference) -> bool {
        // If the mark bit is set, it is live.
        if self.is_marked(object) {
            return true;
        }

        // If we never move objects, look no further.
        if !self.is_movable() {
            return false;
        }

        // If the object is forwarded, it is live, too.
        object_forwarding::is_forwarded::<VM>(object)
    }
    #[cfg(feature = "object_pinning")]
    fn pin_object(&self, object: ObjectReference) -> bool {
        VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC.pin_object::<VM>(object)
    }
    #[cfg(feature = "object_pinning")]
    fn unpin_object(&self, object: ObjectReference) -> bool {
        VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC.unpin_object::<VM>(object)
    }
    #[cfg(feature = "object_pinning")]
    fn is_object_pinned(&self, object: ObjectReference) -> bool {
        VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC.is_object_pinned::<VM>(object)
    }
    fn is_movable(&self) -> bool {
        !self.space_args.never_move_objects
    }

    #[cfg(feature = "sanity")]
    fn is_sane(&self) -> bool {
        true
    }
    fn initialize_object_metadata(&self, _object: ObjectReference, _bytes: usize) {
        #[cfg(feature = "vo_bit")]
        crate::util::metadata::vo_bit::set_vo_bit(_object);
    }
    #[cfg(feature = "vo_bit")]
    fn is_mmtk_object(&self, addr: Address) -> Option<ObjectReference> {
        crate::util::metadata::vo_bit::is_vo_bit_set_for_addr(addr)
    }
    #[cfg(feature = "vo_bit")]
    fn find_object_from_internal_pointer(
        &self,
        ptr: Address,
        max_search_bytes: usize,
    ) -> Option<ObjectReference> {
        // We don't need to search more than the max object size in the immix space.
        let search_bytes = usize::min(super::MAX_IMMIX_OBJECT_SIZE, max_search_bytes);
        crate::util::metadata::vo_bit::find_object_from_internal_pointer::<VM>(ptr, search_bytes)
    }
    fn sft_trace_object(
        &self,
        _queue: &mut OptionObjectQueue,
        _object: ObjectReference,
        _worker: GCWorkerMutRef,
    ) -> ObjectReference {
        panic!("We do not use SFT to trace objects for Immix. sft_trace_object() cannot be used.")
    }

    fn debug_print_object_info(&self, object: ObjectReference) {
        println!("marked  = {}", self.is_marked(object));
        println!(
            "line marked = {}",
            Line::from_unaligned_address(object.to_raw_address()).is_marked(self.mark_state)
        );
        println!(
            "block state = {:?}",
            Block::from_unaligned_address(object.to_raw_address()).get_state()
        );
        object_forwarding::debug_print_object_forwarding_info::<VM>(object);
        self.common.debug_print_object_global_info(object);
    }
}

impl<VM: VMBinding> Space<VM> for ImmixSpace<VM> {
    fn as_space(&self) -> &dyn Space<VM> {
        self
    }
    fn as_sft(&self) -> &(dyn SFT + Sync + 'static) {
        self
    }
    fn get_page_resource(&self) -> &dyn PageResource<VM> {
        &self.pr
    }
    fn maybe_get_page_resource_mut(&mut self) -> Option<&mut dyn PageResource<VM>> {
        Some(&mut self.pr)
    }
    fn common(&self) -> &CommonSpace<VM> {
        &self.common
    }
    fn initialize_sft(&self, sft_map: &mut dyn SFTMap) {
        self.common().initialize_sft(self.as_sft(), sft_map)
    }
    fn release_multiple_pages(&mut self, _start: Address) {
        panic!("immixspace only releases pages enmasse")
    }
    fn set_copy_for_sft_trace(&mut self, _semantics: Option<CopySemantics>) {
        panic!("We do not use SFT to trace objects for Immix. set_copy_context() cannot be used.")
    }

    fn enumerate_objects(&self, enumerator: &mut dyn ObjectEnumerator) {
        object_enum::enumerate_blocks_from_chunk_map::<Block>(enumerator, &self.chunk_map);
    }

    fn clear_side_log_bits(&self) {
        // Remove the following warning if we have a legitimate use case.
        warn!("ImmixSpace::clear_side_log_bits is single-treaded.  Consider clearing side metadata in per-chunk work packets.");

        let log_bit = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
        for chunk in self.chunk_map.all_chunks() {
            log_bit.bzero_metadata(chunk.start(), Chunk::BYTES);
        }
    }

    fn set_side_log_bits(&self) {
        // Remove the following warning if we have a legitimate use case.
        warn!("ImmixSpace::set_side_log_bits is single-treaded.  Consider setting side metadata in per-chunk work packets.");

        let log_bit = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
        for chunk in self.chunk_map.all_chunks() {
            log_bit.bset_metadata(chunk.start(), Chunk::BYTES);
        }
    }
}

impl<VM: VMBinding> crate::policy::gc_work::PolicyTraceObject<VM> for ImmixSpace<VM> {
    fn trace_object<Q: ObjectQueue, const KIND: TraceKind>(
        &self,
        queue: &mut Q,
        object: ObjectReference,
        copy: Option<CopySemantics>,
        worker: &mut GCWorker<VM>,
    ) -> ObjectReference {
        if KIND == TRACE_KIND_TRANSITIVE_PIN {
            self.trace_object_without_moving(queue, object)
        } else if KIND == TRACE_KIND_DEFRAG {
            if Block::containing(object).is_defrag_source() {
                debug_assert!(self.in_defrag());
                debug_assert!(
                    !crate::plan::is_nursery_gc(worker.mmtk.get_plan()),
                    "Calling PolicyTraceObject on Immix in nursery GC"
                );
                self.trace_object_with_opportunistic_copy(
                    queue,
                    object,
                    copy.unwrap(),
                    worker,
                    // This should not be nursery collection. Nursery collection does not use PolicyTraceObject.
                    false,
                )
            } else {
                self.trace_object_without_moving(queue, object)
            }
        } else if KIND == TRACE_KIND_FAST {
            self.trace_object_without_moving(queue, object)
        } else {
            unreachable!()
        }
    }

    fn post_scan_object(&self, object: ObjectReference) {
        if super::MARK_LINE_AT_SCAN_TIME && !super::BLOCK_ONLY {
            debug_assert!(self.in_space(object));
            self.mark_lines(object);
        }
    }

    #[allow(clippy::if_same_then_else)] // DEFAULT_TRACE needs a workaround which is documented below.
    fn may_move_objects<const KIND: TraceKind>() -> bool {
        if KIND == TRACE_KIND_DEFRAG {
            true
        } else if KIND == TRACE_KIND_FAST || KIND == TRACE_KIND_TRANSITIVE_PIN {
            false
        } else if KIND == DEFAULT_TRACE {
            // FIXME: This is hacky. When we do a default trace, this should be a nonmoving space.
            // The only exception is the nursery GC for sticky immix, for which, we use default trace.
            // This function is only used for PlanTrace, and for sticky immix nursery GC, we use
            // GenNurseryTrace. So it still works. But this is quite hacky anyway.
            // See https://github.com/mmtk/mmtk-core/issues/1314 for details.
            false
        } else {
            unreachable!()
        }
    }
}

impl<VM: VMBinding> ImmixSpace<VM> {
    #[allow(unused)]
    const UNMARKED_STATE: u8 = 0;
    const MARKED_STATE: u8 = 1;

    /// Get side metadata specs
    fn side_metadata_specs() -> Vec<SideMetadataSpec> {
        metadata::extract_side_metadata(&if super::BLOCK_ONLY {
            vec![
                MetadataSpec::OnSide(Block::DEFRAG_STATE_TABLE),
                MetadataSpec::OnSide(Block::MARK_TABLE),
                *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC,
                *VM::VMObjectModel::LOCAL_FORWARDING_BITS_SPEC,
                *VM::VMObjectModel::LOCAL_FORWARDING_POINTER_SPEC,
                #[cfg(feature = "object_pinning")]
                *VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC,
            ]
        } else {
            vec![
                MetadataSpec::OnSide(Line::MARK_TABLE),
                MetadataSpec::OnSide(Block::DEFRAG_STATE_TABLE),
                MetadataSpec::OnSide(Block::MARK_TABLE),
                *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC,
                *VM::VMObjectModel::LOCAL_FORWARDING_BITS_SPEC,
                *VM::VMObjectModel::LOCAL_FORWARDING_POINTER_SPEC,
                #[cfg(feature = "object_pinning")]
                *VM::VMObjectModel::LOCAL_PINNING_BIT_SPEC,
            ]
        })
    }

    pub fn new(
        args: crate::policy::space::PlanCreateSpaceArgs<VM>,
        mut space_args: ImmixSpaceArgs,
    ) -> Self {
        if args.unlog_traced_object {
            assert!(
                args.constraints.needs_log_bit,
                "Invalid args when the plan does not use log bit"
            );
        }

        // Make sure we override the space args if we force non moving Immix
        if cfg!(feature = "immix_non_moving") && !space_args.never_move_objects {
            info!(
                "Overriding never_moves_objects for Immix Space {}, as the immix_non_moving feature is set. Block size: 2^{}",
                args.name,
                Block::LOG_BYTES,
            );
            space_args.never_move_objects = true;
        }

        // validate features
        if super::BLOCK_ONLY {
            assert!(
                space_args.never_move_objects,
                "Block-only immix must not move objects"
            );
        }
        assert!(
            Block::LINES / 2 <= u8::MAX as usize - 2,
            "Number of lines in a block should not exceed BlockState::MARK_MARKED"
        );

        #[cfg(feature = "vo_bit")]
        vo_bit::helper::validate_config::<VM>();
        let vm_map = args.vm_map;
        let scheduler = args.scheduler.clone();
        let common =
            CommonSpace::new(args.into_policy_args(true, false, Self::side_metadata_specs()));
        let space_index = common.descriptor.get_index();
        ImmixSpace {
            pr: if common.vmrequest.is_discontiguous() {
                BlockPageResource::new_discontiguous(
                    Block::LOG_PAGES,
                    vm_map,
                    scheduler.num_workers(),
                )
            } else {
                BlockPageResource::new_contiguous(
                    Block::LOG_PAGES,
                    common.start,
                    common.extent,
                    vm_map,
                    scheduler.num_workers(),
                )
            },
            common,
            chunk_map: ChunkMap::new(space_index),
            line_mark_state: AtomicU8::new(Line::RESET_MARK_STATE),
            line_unavail_state: AtomicU8::new(Line::RESET_MARK_STATE),
            lines_consumed: AtomicUsize::new(0),
            unswept_blocks: std::sync::Mutex::new(Vec::new()),
            unswept_young: std::sync::Mutex::new(Vec::new()),
            deferred_post_pause_packets: std::sync::Mutex::new(Vec::new()),
            live_bytes: &LIVE_BYTES_TOTAL,
            finalizer_reclaim_gate: std::sync::atomic::AtomicBool::new(false),
            live_bytes_prev: std::sync::atomic::AtomicUsize::new(0),
            pending_blocks: std::sync::Mutex::new(Vec::new()),
            unswept_nonempty: std::sync::atomic::AtomicBool::new(false),
            unswept_nursery: std::sync::Mutex::new(Vec::new()),
            nursery_unswept_nonempty: std::sync::atomic::AtomicBool::new(false),
            nursery_lines_claimed: std::sync::atomic::AtomicUsize::new(0),
            full_blocks: std::sync::Mutex::new(Vec::new()),
            reusable_blocks: ReusableBlockPool::new(scheduler.num_workers()),
            defrag: Defrag::default(),
            // Set to the correct mark state when inititialized. We cannot rely on prepare to set it (prepare may get skipped in nursery GCs).
            mark_state: Self::MARKED_STATE,
            scheduler: scheduler.clone(),
            space_args,
        }
    }

    /// Flush the thread-local queues in BlockPageResource
    pub fn flush_page_resource(&self) {
        self.reusable_blocks.flush_all();
        #[cfg(target_pointer_width = "64")]
        self.pr.flush_all()
    }

    /// Get the number of defrag headroom pages.
    pub fn defrag_headroom_pages(&self) -> usize {
        self.defrag.defrag_headroom_pages(self)
    }

    /// Check if current GC is a defrag GC.
    pub fn in_defrag(&self) -> bool {
        self.defrag.in_defrag()
    }

    /// check if the current GC should do defragmentation.
    pub fn decide_whether_to_defrag(
        &self,
        emergency_collection: bool,
        collect_whole_heap: bool,
        collection_attempts: usize,
        user_triggered_collection: bool,
        full_heap_system_gc: bool,
    ) -> bool {
        self.defrag.decide_whether_to_defrag(
            self.is_defrag_enabled(),
            emergency_collection,
            collect_whole_heap,
            collection_attempts,
            user_triggered_collection,
            self.reusable_blocks.len() == 0,
            full_heap_system_gc,
            *self.common.options.immix_always_defrag,
        );
        self.defrag.in_defrag()
    }

    /// Get work packet scheduler
    fn scheduler(&self) -> &GCWorkScheduler<VM> {
        &self.scheduler
    }

    pub(crate) fn prepare(
        &mut self,
        major_gc: bool,
        plan_stats: Option<StatsForDefrag>,
        unlog_bits_op: UnlogBitsOperation,
    ) {
        if major_gc {
            // Update mark_state
            if VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.is_on_side() {
                self.mark_state = Self::MARKED_STATE;
            } else {
                // For header metadata, we use cyclic mark bits.
                unimplemented!("cyclic mark bits is not supported at the moment");
            }

            // Fresh live accounting for a full trace (see
            // `prepare_concurrent_initial`; nursery collections keep
            // accumulating since their trace only covers new objects).
            self.live_bytes.store(0, std::sync::atomic::Ordering::SeqCst);

            // Prepare defrag info
            if self.is_defrag_enabled() {
                self.defrag.prepare(self, plan_stats.unwrap());
            }

            // Prepare each block for GC
            let threshold = self.defrag.defrag_spill_threshold.load(Ordering::Acquire);
            // # Safety: ImmixSpace reference is always valid within this collection cycle.
            let space = unsafe { &*(self as *const Self) };
            let work_packets = self.chunk_map.generate_tasks(|chunk| {
                Box::new(PrepareBlockState {
                    space,
                    chunk,
                    defrag_threshold: if space.in_defrag() {
                        Some(threshold)
                    } else {
                        None
                    },
                    unlog_bits_op,
                })
            });
            self.scheduler().work_buckets[WorkBucketStage::Prepare].bulk_add(work_packets);

            // GENERATIONAL: marks persist between collections (see
            // `prepare_concurrent_initial`); a full-heap trace must start
            // from clean mark bits, cleared in-pause.
            let clear_packets = self.chunk_map.generate_tasks(|chunk| {
                Box::new(ClearChunkMarks::<VM> {
                    chunk,
                    _p: std::marker::PhantomData,
                })
            });
            self.scheduler().work_buckets[WorkBucketStage::Prepare].bulk_add(clear_packets);

            if !super::BLOCK_ONLY {
                self.line_mark_state.fetch_add(1, Ordering::AcqRel);
                if self.line_mark_state.load(Ordering::Acquire) > Line::MAX_MARK_STATE {
                    self.line_mark_state
                        .store(Line::RESET_MARK_STATE, Ordering::Release);
                }
            }
        }

        #[cfg(feature = "vo_bit")]
        if vo_bit::helper::need_to_clear_vo_bits_before_tracing::<VM>() {
            let maybe_scope = if major_gc {
                // If it is major GC, we always clear all VO bits because we are doing full-heap
                // tracing.
                Some(VOBitsClearingScope::FullGC)
            } else if self.space_args.mixed_age {
                // StickyImmix nursery GC.
                // Some lines (or blocks) contain only young objects,
                // while other lines (or blocks) contain only old objects.
                if super::BLOCK_ONLY {
                    // Block only.  Young objects are only allocated into fully empty blocks.
                    // Only clear unmarked blocks.
                    Some(VOBitsClearingScope::BlockOnly)
                } else {
                    // Young objects are allocated into empty lines.
                    // Only clear unmarked lines.
                    let line_mark_state = self.line_mark_state.load(Ordering::SeqCst);
                    Some(VOBitsClearingScope::Line {
                        state: line_mark_state,
                    })
                }
            } else {
                // GenImmix nursery GC.  We do nothing to the ImmixSpace because the nursery is a
                // separate CopySpace.  It'll clear its own VO bits.
                None
            };

            if let Some(scope) = maybe_scope {
                let work_packets = self
                    .chunk_map
                    .generate_tasks(|chunk| Box::new(ClearVOBitsAfterPrepare { chunk, scope }));
                self.scheduler.work_buckets[WorkBucketStage::ClearVOBits].bulk_add(work_packets);
            }
        }
    }

    /// Release for the immix space.
    pub(crate) fn release(
        &mut self,
        major_gc: bool,
        unlog_bits_op: UnlogBitsOperation,
        concurrent_sweep: bool,
    ) {
        if major_gc {
            // Update line_unavail_state for hole searching after this GC.
            if !super::BLOCK_ONLY {
                self.line_unavail_state.store(
                    self.line_mark_state.load(Ordering::Acquire),
                    Ordering::Release,
                );
            }
        }
        // Clear reusable blocks list
        if !super::BLOCK_ONLY && !concurrent_sweep {
            self.reusable_blocks.reset();
        }
        // FIX E (lazy sweep): O(mutators) pause work -- splice abandoned and
        // full blocks into the unswept list.  Triage happens on the allocator
        // slow path (`lazy_triage_some`).
        if concurrent_sweep {
            // GENERATIONAL: mark bits are NOT cleared after this pause.  They
            // persist between collections as the old-set indicator (minors
            // terminate on them); the next InitialMark/Full clears them
            // in-pause before its own trace.  Unlog-bit maintenance is
            // precise (trace-time, float promotion below, remset re-arm), so
            // no deferred chunk packets remain here.
            let t0 = crate::diag::now_ns();
            if !matches!(unlog_bits_op, UnlogBitsOperation::NoOp) {
                let space = unsafe { &*(self as *const Self) };
                let mut deferred = self.deferred_post_pause_packets.lock().unwrap();
                for chunk in self.chunk_map.all_chunks() {
                    deferred.push(Box::new(UnlogBitsChunk {
                        space,
                        chunk,
                        op: unlog_bits_op,
                    }) as _);
                }
            }
            crate::diag::record_max(
                &crate::diag::UNLOG_MAX_NS,
                crate::diag::now_ns().saturating_sub(t0),
            );
            // PATH 2: release is fully deferred; the GC trigger accounts for
            // unswept-reclaimable memory instead (see `reclaimable_pages`).
            self.live_bytes_prev.store(
                self.live_bytes.load(std::sync::atomic::Ordering::SeqCst),
                std::sync::atomic::Ordering::SeqCst,
            );
            // Age the generations: last cycle's float becomes triageable,
            // this cycle's float becomes the new young generation.
            let mut young = self.unswept_young.lock().unwrap();
            {
                let mut unswept = self.unswept_blocks.lock().unwrap();
                unswept.append(&mut young);
                if !unswept.is_empty() {
                    self.unswept_nonempty.store(true, Ordering::Relaxed);
                }
            }
            // Drain the reusable pool: pool entries must not outlive the
            // window -- tracing and PrepareBlockState mutate the states of
            // pool-resident blocks (eager sweep enforced this via reset()).
            // Drained blocks re-classify from the unswept list next window.
            while let Some(b) = self.reusable_blocks.pop() {
                young.push(b);
            }
            {
                let mut pending = self.pending_blocks.lock().unwrap();
                // ALWAYS-ON BARRIER: promote the cycle's float.  Blocks
                // claimed since InitialMark hold allocate-black objects
                // (marked-live, never traced, so never trace-armed); after
                // this pause they are old and their mutations must be logged.
                // Arm them IN-PAUSE: once mutators resume, a disarmed old
                // object's write would skip the barrier.  (Blocks claimed
                // before InitialMark were armed in that pause; re-arming is
                // idempotent.)
                if self.common.needs_log_bit {
                    let unlog = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
                    for block in pending.iter() {
                        unlog.bset_metadata(block.start(), Block::BYTES);
                    }
                }
                young.append(&mut pending);
            }
            young.append(&mut self.full_blocks.lock().unwrap());
            // Uncensused nursery-list blocks were re-proven by this major
            // (traced + line-marked); their object-mark census is invalid
            // after the InitialMark clear, so route them through the regular
            // line-census aging pipeline instead.
            young.append(&mut self.unswept_nursery.lock().unwrap());
            self.nursery_unswept_nonempty
                .store(false, std::sync::atomic::Ordering::Relaxed);
            drop(young);
            self.nursery_lines_claimed
                .store(0, Ordering::Relaxed);
            // Release is fully deferred (float-budget trigger keeps the
            // reserved-pages signal irrelevant); the aged generation is
            // drained by allocation-time triage and the drain-before-OOM loop.
            self.lines_consumed.store(0, Ordering::Relaxed);
            return;
        }
        // Sweep chunks and blocks
        let work_packets = self.generate_sweep_tasks(unlog_bits_op, false);
        self.scheduler().work_buckets[WorkBucketStage::Release].bulk_add(work_packets);

        self.lines_consumed.store(0, Ordering::Relaxed);
    }

    /// LEG 1: slim InitialMark prepare for the concurrent lazy-sweep plan.
    /// The ONLY per-chunk work that must happen inside the InitialMark pause
    /// is arming the SATB unlog bits (the pause IS the snapshot boundary;
    /// arming earlier would let mutators consume bits pre-marking, arming
    /// later would miss writes).  Mark-bit clearing was deferred to
    /// post-FinalMark concurrent packets (mark bits are untouched between
    /// cycles), and block-state resets are skipped entirely: lazy triage
    /// classifies by LINE marks, pool pops tolerate stale states, and defrag
    /// is not used by the concurrent pauses.
    pub(crate) fn prepare_concurrent_initial(&mut self) {
        if VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.is_on_side() {
            self.mark_state = Self::MARKED_STATE;
        } else {
            unimplemented!("cyclic mark bits is not supported at the moment");
        }

        // `live_bytes` accumulates at every marked object and is snapshotted
        // into `live_bytes_prev` at release; without a per-cycle reset it
        // grows monotonically and poisons every consumer (float budget,
        // pacing live estimate).
        self.live_bytes.store(0, std::sync::atomic::Ordering::SeqCst);

        // ALWAYS-ON BARRIER: arm the blocks claimed since the last collection
        // (they hold the young objects, born unarmed).  The pause IS the SATB
        // snapshot boundary: every live object must be armed when marking
        // starts, or its overwritten fields escape the snapshot.  Block
        // ranges are armed whole; unallocated tails are unreachable for
        // allocation until they cycle through FinalMark aging and are
        // disarmed at re-claim.  Old blocks stay armed from trace-time
        // arming, the FinalMark float promotion, and the remset drain re-arm.
        if self.common.needs_log_bit {
            let unlog = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
            for block in self.pending_blocks.lock().unwrap().iter() {
                unlog.bset_metadata(block.start(), Block::BYTES);
            }
        }

        // AUDIT ORACLE (MMTK_AUDIT_UNLOG): the live=>armed snapshot
        // invariant, checked against the persisted old set BEFORE the mark
        // bits are cleared below (and before the clear packets can run):
        // every MARKED object must be armed at InitialMark.  (The historic
        // every-bit-armed form is obsolete: arming is per-object now, so
        // non-object granules and dead ranges are legitimately zero.  Young
        // objects are covered by the whole-range pending arm above.)
        if std::env::var_os("MMTK_AUDIT_UNLOG").is_some() {
            let mark = VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.extract_side_spec();
            let mut bad = 0usize;
            for chunk in self.chunk_map.all_chunks() {
                mark.scan_non_zero_values::<u8>(chunk.start(), chunk.end(), &mut |addr| {
                    if let Some(obj) = ObjectReference::from_raw_address(addr) {
                        if !VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                            .is_unlogged::<VM>(obj, Ordering::Relaxed)
                        {
                            if bad < 5 {
                                eprintln!("[unlog-audit] marked-but-DISARMED {:?}", obj);
                            }
                            bad += 1;
                        }
                    }
                });
            }
            if bad > 0 {
                eprintln!("[unlog-audit] AT INIT: {bad} marked-but-disarmed objects");
            } else {
                eprintln!("[unlog-audit] AT INIT: live=>armed holds");
            }
        }

        // GENERATIONAL: clear the object mark bits IN-PAUSE, right before
        // this cycle's trace.  Marks persist between collections as the
        // old-set indicator for minors, so the clear cannot be deferred
        // post-pause as before; parallel per-chunk packets in the (open)
        // Prepare bucket keep the cost off the critical path.
        {
            let packets = self.chunk_map.generate_tasks(|chunk| {
                Box::new(ClearChunkMarks::<VM> {
                    chunk,
                    _p: std::marker::PhantomData,
                })
            });
            self.scheduler().work_buckets[WorkBucketStage::Prepare].bulk_add(packets);
        }

        // DIAG (MMTK_CHECK_STALE_MARKS): OBSOLETE under mark persistence --
        // marks now survive between collections by design (the old set), and
        // the in-pause ClearChunkMarks packets scheduled above run after this
        // function returns.  Kept for layout probing only; expect nonzero
        // counts.
        if std::env::var_os("MMTK_CHECK_STALE_MARKS").is_some() {
            // Layout probe: metadata addresses of the three specs for one chunk.
            if let Some(chunk) = self.chunk_map.all_chunks().next() {
                use crate::util::metadata::side_metadata::helpers::address_to_meta_address;
                if let crate::util::metadata::MetadataSpec::OnSide(mark) =
                    *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC
                {
                    let log = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
                    let line = &Line::MARK_TABLE;
                    eprintln!(
                        "[meta-layout] chunk={:?} log_bit={:?}..(+{:#x}) line_mark={:?}..(+{:#x}) obj_mark={:?}..(+{:#x})",
                        chunk.start(),
                        address_to_meta_address(log, chunk.start()),
                        (Chunk::BYTES >> log.log_bytes_in_region) >> (3 - log.log_num_of_bits),
                        address_to_meta_address(line, chunk.start()),
                        (Chunk::BYTES >> line.log_bytes_in_region) << line.log_num_of_bits.saturating_sub(3),
                        address_to_meta_address(&mark, chunk.start()),
                        (Chunk::BYTES >> mark.log_bytes_in_region) >> (3 - mark.log_num_of_bits),
                    );
                }
            }
            if let crate::util::metadata::MetadataSpec::OnSide(side) =
                *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC
            {
                let mut stale_chunks = 0usize;
                let mut stale_bytes = 0usize;
                let mut first: Option<(Address, usize)> = None;
                for chunk in self.chunk_map.all_chunks() {
                    let meta_start = crate::util::metadata::side_metadata::helpers::address_to_meta_address(
                        &side,
                        chunk.start(),
                    );
                    let meta_bytes =
                        (Chunk::BYTES >> side.log_bytes_in_region) >> (3 - side.log_num_of_bits);
                    let mut nz = 0usize;
                    for i in 0..meta_bytes {
                        let b: u8 = unsafe { (meta_start + i).load::<u8>() };
                        if b != 0 {
                            nz += 1;
                        }
                    }
                    if nz > 0 {
                        stale_chunks += 1;
                        stale_bytes += nz;
                        if first.is_none() {
                            first = Some((chunk.start(), nz));
                        }
                    }
                }
                if stale_bytes > 0 {
                    // Value histogram of the first stale chunk's meta bytes.
                    if let Some((cstart, _)) = first {
                        let meta_start = crate::util::metadata::side_metadata::helpers::address_to_meta_address(&side, cstart);
                        let meta_bytes = (Chunk::BYTES >> side.log_bytes_in_region) >> (3 - side.log_num_of_bits);
                        let mut h = std::collections::HashMap::new();
                        for i in 0..meta_bytes {
                            let b: u8 = unsafe { (meta_start + i).load::<u8>() };
                            *h.entry(b).or_insert(0usize) += 1;
                        }
                        let mut hv: Vec<_> = h.into_iter().collect();
                        hv.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
                        eprintln!("[stale-vals] top bytes: {:?}", &hv[..hv.len().min(6)]);
                    }
                    eprintln!(
                        "[stale-marks] AT INIT: {} chunks with {} nonzero meta bytes; first chunk {:?} nz={}",
                        stale_chunks,
                        stale_bytes,
                        first.map(|f| f.0),
                        first.map(|f| f.1).unwrap_or(0)
                    );
                } else {
                    eprintln!("[stale-marks] AT INIT: clean");
                }
            }
        }

        // DIAG (MMTK_INPAUSE_MARK_CLEAR): re-instate the in-pause object
        // mark-bit clear to test whether stale mark bits at InitialMark are
        // the cause of the bootstrap SATB corruption.
        if std::env::var_os("MMTK_INPAUSE_MARK_CLEAR").is_some() {
            let clear_packets: Vec<Box<dyn GCWork<VM>>> = self
                .chunk_map
                .all_chunks()
                .map(|chunk| {
                    Box::new(ClearChunkMarks::<VM> {
                        chunk,
                        _p: std::marker::PhantomData,
                    }) as _
                })
                .collect();
            self.scheduler().work_buckets[WorkBucketStage::Prepare].bulk_add(clear_packets);
        }

        if !super::BLOCK_ONLY {
            self.line_mark_state.fetch_add(1, Ordering::AcqRel);
            if self.line_mark_state.load(Ordering::Acquire) > Line::MAX_MARK_STATE {
                self.line_mark_state
                    .store(Line::RESET_MARK_STATE, Ordering::Release);
            }
        }
    }

    /// LEG 1: hand the deferred post-pause packets to the plan for
    /// scheduling after the pause.
    pub(crate) fn take_deferred_packets(&self) -> Vec<Box<dyn GCWork<VM>>> {
        std::mem::take(&mut *self.deferred_post_pause_packets.lock().unwrap())
    }

    /// LEG 1: add a packet to run concurrently after the current pause.
    pub(crate) fn defer_post_pause_packet(&self, packet: Box<dyn GCWork<VM>>) {
        self.deferred_post_pause_packets
            .lock()
            .unwrap()
            .push(packet);
    }

    /// This is called when a GC finished.
    /// Return whether this GC was a defrag GC, as a plan may want to know this.
    pub fn end_of_gc(&mut self) -> bool {
        let did_defrag = self.defrag.in_defrag();
        if self.is_defrag_enabled() {
            self.defrag.reset_in_defrag();
        }
        did_defrag
    }

    /// Generate chunk sweep tasks
    fn generate_sweep_tasks(&self, unlog_bits_op: UnlogBitsOperation, lazy: bool) -> Vec<Box<dyn GCWork<VM>>> {
        self.defrag.mark_histograms.lock().clear();
        // # Safety: ImmixSpace reference is always valid within this collection cycle.
        let space = unsafe { &*(self as *const Self) };
        let epilogue = Arc::new(FlushPageResource {
            space,
            counter: AtomicUsize::new(0),
        });
        let tasks = self.chunk_map.generate_tasks(|chunk| {
            Box::new(SweepChunk {
                lazy,
                space,
                chunk,
                unlog_bits_op,
                epilogue: epilogue.clone(),
            })
        });
        epilogue.counter.store(tasks.len(), Ordering::SeqCst);
        tasks
    }

    /// Release a block.
    pub fn release_block(&self, block: Block) {
        block.deinit();
        self.pr.release_block(block);
    }

    /// Allocate a clean block.
    pub fn get_clean_block(
        &self,
        tls: VMThread,
        copy: bool,
        alloc_options: AllocationOptions,
    ) -> Option<Block> {
        let block_address = self.acquire(tls, Block::PAGES, alloc_options);
        if block_address.is_zero() {
            return None;
        }
        self.defrag.notify_new_clean_block(copy);
        let block = Block::from_aligned_address(block_address);
        crate::diag::CLEAN_BLOCKS.fetch_add(1, Ordering::SeqCst);
        block.init(copy);
        // PATH 1: allocate-black blocks must not look Unmarked to the
        // FinalMark block-state release pass -- their lines are marked at
        // acquisition but tracing never visits them.
        if self.should_allocate_as_live() {
            block.set_state(BlockState::Marked);
        }
        // ALWAYS-ON BARRIER: no chunk-level arming.  Objects are born unarmed
        // (the allocator disarms every claimed range); arming is precise:
        // trace-time (`unlog_traced_object`), the in-pause arming of blocks
        // claimed since the last collection (InitialMark makes the young part
        // of the snapshot; FinalMark promotes the cycle's float), and the
        // remset drain re-arm.
        self.chunk_map.set_allocated(block.chunk(), true);
        self.lines_consumed
            .fetch_add(Block::LINES, Ordering::SeqCst);
        self.nursery_lines_claimed
            .fetch_add(Block::LINES, Ordering::Relaxed);
        Some(block)
    }

    /// Pop a reusable block from the reusable block list.
    /// FIX E: pop one chunk from the unswept snapshot and triage its blocks
    /// with the same two-epoch line predicate as hole search (a line is live
    /// iff marked with the current or previous cycle's state), so this is
    /// sound at any time, including while the next cycle's marking runs.
    /// Dead blocks go back to the page resource; holed blocks to the reusable
    /// pool.  VO/pin bits are NOT touched here -- they are cleared at reuse
    /// (`get_clean_block` / `acquire_recyclable_lines`).  Returns false when
    /// no unswept chunks remain.
    /// FIX E: record an acquired block.  It joins the unswept list at the
    /// next FinalMark, by which time its owner has been reset and its live
    /// contents are line-marked.
    pub fn record_acquired(&self, block: Block) {
        self.pending_blocks.lock().unwrap().push(block);
    }

    /// FIX E: triage up to `budget` unswept blocks (allocation-driven lazy
    /// sweep).  Everything in `unswept_blocks` has survived a full marking, so
    /// live lines are marked (two-epoch predicate) and classification is safe
    /// concurrently with mutators and with the next cycle's marking.
    /// Returns false when the unswept list is empty.
    /// PATH 2: pages the lazy sweep will eventually return: reserved minus
    /// last cycle's live estimate minus the current cycle's allocate-black
    /// float (blocks acquired since FinalMark, all in `pending_blocks`).
    pub fn reclaimable_pages(&self) -> usize {
        // Only the aged unswept generation is reclaimable; subtract the live
        // estimate since its blocks may also hold surviving objects.
        let old_pages = self.unswept_blocks.lock().unwrap().len() * (Block::BYTES >> 12);
        let live = self
            .live_bytes_prev
            .load(std::sync::atomic::Ordering::Relaxed)
            >> 12;
        old_pages.saturating_sub(live)
    }

    /// Pages of the current cycle's float: blocks acquired since FinalMark.
    pub fn float_pages(&self) -> usize {
        self.pending_blocks.lock().unwrap().len() * (Block::BYTES >> 12)
    }

    pub fn live_prev_pages(&self) -> usize {
        self.live_bytes_prev
            .load(std::sync::atomic::Ordering::Relaxed)
            >> 12
    }

    /// Current-cycle live accumulation in pages (complete after a major's
    /// trace; between majors it also carries minor promotion).
    pub fn live_now_pages(&self) -> usize {
        self.live_bytes.load(std::sync::atomic::Ordering::Relaxed) >> 12
    }

    pub fn has_unswept(&self) -> bool {
        !self.unswept_blocks.lock().unwrap().is_empty()
    }

    /// NURSERY SWEEP (in-pause, minor collections): drain `pending_blocks`
    /// (= every block touched by allocation since the last collection) and
    /// reclaim its dead lines, using OBJECT mark bits as the liveness
    /// source.  Line marks cannot serve here: claims line-mark their ranges
    /// as double-claim protection for the lazy major pipeline, so a
    /// claim-marked dead line is indistinguishable from a live one.  Object
    /// marks are exact at this point in the pause: the nursery trace just
    /// marked survivors, old objects' marks persist from the last major, and
    /// claim noise never touches them.  Line marks are then REWRITTEN to
    /// match (live -> current epoch, dead -> cleared) so the hole-search and
    /// triage predicates continue to see the truth.
    /// Minor-pause release work: drain the nursery (pending blocks) and
    /// schedule the census as PARALLEL packets in the open Release bucket.
    /// The census is the only minor-pause work that scales with nursery
    /// size, it parallelizes perfectly (independent blocks), and it has
    /// worker-side cache affinity (the trace workers wrote the marks it
    /// reads) -- measured: serial-in-pause cost ~0.35ms/pause and
    /// claim-time (mutator) cost ~2x that in cross-CCX metadata fills.
    pub(crate) fn sweep_nursery_blocks(&self) {
        let blocks: Vec<Block> = std::mem::take(&mut *self.pending_blocks.lock().unwrap());
        self.nursery_lines_claimed
            .store(0, std::sync::atomic::Ordering::Relaxed);
        if blocks.is_empty() {
            return;
        }
        // MMTK_LAZY_NURSERY=1: skip the in-pause census entirely; blocks are
        // classified at claim time (`nursery_census_some`, with the all-dead
        // fast path).  A/B knob for the pause-floor experiment.
        {
            // CONCURRENT FINALIZER SWEEP: the in-pause census bzeroes and
            // releases all-dead blocks, but the deferred sweep may still
            // read (and resurrect) dead objects in them.  While the gate is
            // up, divert everything to the lazy path, whose entry points
            // honor the gate.
            let finalizer_gated = self
                .finalizer_reclaim_gate
                .load(std::sync::atomic::Ordering::SeqCst);
            static LAZY: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if finalizer_gated
                || *LAZY.get_or_init(|| std::env::var_os("MMTK_LAZY_NURSERY").is_some())
            {
                let mut q = self.unswept_nursery.lock().unwrap();
                q.extend(blocks);
                self.nursery_unswept_nonempty
                    .store(true, std::sync::atomic::Ordering::Relaxed);
                return;
            }
        }
        let space = unsafe { &*(self as *const Self) };
        // The line-state census costs ~100ns/block; one packet per ~1000
        // blocks costs less in wake edges than 16 packets of trivial work.
        let chunk = blocks.len().max(1);
        let _ = chunk;
        let chunk = (blocks.len() / 2).max(1024);
        let packets: Vec<Box<dyn GCWork<VM>>> = blocks
            .chunks(chunk)
            .map(|c| {
                Box::new(CensusNurseryBlocks {
                    space,
                    blocks: c.to_vec(),
                }) as _
            })
            .collect();
        self.scheduler().work_buckets[WorkBucketStage::Release].bulk_add(packets);
    }

    /// LAZY NURSERY CENSUS (allocation-paid): classify up to `budget` blocks
    /// from the last minor(s) by walking marked object starts and painting
    /// their extents (see the span-aware liveness rationale below), rewrite
    /// line marks to match, then release dead blocks and pool holed ones.
    /// Sound whenever no marking is in flight: object marks are stable
    /// between collections (minors only add marks; the census list is never
    /// allocated into).  During a major's marking the InitialMark clear has
    /// invalidated the old set, so defer (same idle-only guard as the major
    /// triage); FinalMark re-proves these blocks and ages them into the
    /// regular unswept pipeline instead.
    /// Mark an object reached by the deferred finalizer sweep so lazy reuse
    /// keeps it (see `ConcurrentPlan::finalizer_resurrect_object`).  Returns
    /// whether the object was newly marked.
    pub(crate) fn resurrect_object(&self, object: ObjectReference) -> bool {
        if self.attempt_mark(object, self.mark_state) {
            self.mark_lines(object);
            return true;
        }
        false
    }

    pub fn nursery_census_some(&self, budget: usize) -> bool {
        if self
            .finalizer_reclaim_gate
            .load(std::sync::atomic::Ordering::SeqCst)
        {
            return false;
        }
        if !self
            .nursery_unswept_nonempty
            .load(std::sync::atomic::Ordering::Relaxed)
        {
            return false;
        }
        // Idle-only: cur != unavail exactly while a major cycle is open.
        let cur = self.line_mark_state.load(Ordering::Acquire);
        let unavail = self.line_unavail_state.load(Ordering::Acquire);
        if cur != unavail {
            return false;
        }
        let blocks: Vec<Block> = {
            let mut q = self.unswept_nursery.lock().unwrap();
            let n = q.len().min(budget);
            if n == 0 {
                self.nursery_unswept_nonempty
                    .store(false, std::sync::atomic::Ordering::Relaxed);
                return false;
            }
            let at = q.len() - n;
            let taken = q.split_off(at);
            if q.is_empty() {
                self.nursery_unswept_nonempty
                    .store(false, std::sync::atomic::Ordering::Relaxed);
            }
            taken
        };
        self.census_nursery_blocks(blocks);
        true
    }

    fn census_nursery_blocks(&self, blocks: Vec<Block>) {
        let state = self.line_mark_state.load(Ordering::Acquire);
        let mut dead: Vec<Block> = Vec::new();
        let mut freed_lines = 0usize;
        let mut live_blocks = 0usize;
        for block in blocks {
            debug_assert_ne!(block.get_state(), BlockState::Unallocated);
            // LINE-STATE CENSUS: liveness is read directly from the line
            // marks.  Scan-time line marking painted every survivor's full
            // extent with the current epoch (so straddle tails are covered),
            // recycled blocks' old-live lines carry the last major's epoch
            // (same value between majors), and idle-window claim protection
            // uses the distinct CLAIMED sentinel -- so a line is live iff it
            // is epoch-marked, with no object-mark scan and no header reads
            // (the survivor-heavy census previously cost 5-29ms per startup
            // minor in cold `get_current_size` reads).
            let mark_data = block.line_mark_table();
            let mut live_lines: usize = 0;
            for i in 0..mark_data.len() {
                if mark_data.get(i) == state {
                    live_lines += 1;
                }
            }
            // Fast path for the dominant case: a fully dead block needs no
            // per-line rewriting -- clear its line marks in one metadata
            // bzero and release it.
            if live_lines == 0 {
                Line::MARK_TABLE.bzero_metadata(block.start(), Block::BYTES);
                freed_lines += Block::LINES;
                block.deinit();
                dead.push(block);
                continue;
            }
            // Mixed block: clear non-epoch lines (CLAIMED noise and stale
            // states) so hole search sees the reclaimed lines as free.
            for (i, line) in block.lines().enumerate() {
                if mark_data.get(i) != state {
                    line.mark(0);
                    freed_lines += 1;
                }
            }
            if live_lines < Block::LINES {
                block.set_state(BlockState::Reusable {
                    unavailable_lines: live_lines as _,
                });
                self.reusable_blocks.push(block);
                live_blocks += 1;
            } else {
                block.set_state(BlockState::Marked);
                self.full_blocks.lock().unwrap().push(block);
                live_blocks += 1;
            }
        }
        // DIAG (MMTK_NURSERY_TRACE): per-census ledger.
        {
            static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
            if *TRACE.get_or_init(|| std::env::var_os("MMTK_NURSERY_TRACE").is_some()) {
                eprintln!(
                    "[nursery-census] blocks={} dead={} kept={} freed_lines={}",
                    dead.len() + live_blocks,
                    dead.len(),
                    live_blocks,
                    freed_lines,
                );
            }
        }
        crate::diag::NURSERY_SWEPT_BLOCKS.fetch_add(dead.len(), Ordering::Relaxed);
        crate::diag::NURSERY_KEPT_BLOCKS.fetch_add(live_blocks, Ordering::Relaxed);
        crate::diag::NURSERY_FREED_LINES.fetch_add(freed_lines, Ordering::Relaxed);
        if !dead.is_empty() {
            self.pr.release_blocks_batch(&dead);
        }
    }

    /// Real nursery size in pages: free lines handed to allocators since
    /// the last collection (see `nursery_lines_claimed`).
    pub fn nursery_claimed_pages(&self) -> usize {
        self.nursery_lines_claimed
            .load(std::sync::atomic::Ordering::Relaxed)
            / (4096 / Line::BYTES)
    }

    /// Bytes promoted by minors since the last major: `live_bytes` counts
    /// every first-time `attempt_mark` (a minor's successful marks are
    /// exactly its promotions; old objects short-circuit), is reset at
    /// InitialMark/Full prepare, and `live_bytes_prev` snapshots the major's
    /// own total at its release -- so the delta is pure minor promotion.
    pub fn promoted_bytes_since_major(&self) -> usize {
        self.live_bytes
            .load(std::sync::atomic::Ordering::Relaxed)
            .saturating_sub(
                self.live_bytes_prev
                    .load(std::sync::atomic::Ordering::Relaxed),
            )
    }

    pub fn lazy_triage_some(&self, budget: usize) -> bool {
        if self
            .finalizer_reclaim_gate
            .load(std::sync::atomic::Ordering::SeqCst)
        {
            return false;
        }
        if !self.unswept_nonempty.load(Ordering::Relaxed) {
            return false;
        }
        let t0 = crate::diag::now_ns();
        let r = self.lazy_triage_some_inner(budget);
        let d = crate::diag::now_ns().saturating_sub(t0);
        crate::diag::record_max(&crate::diag::TRIAGE_MAX_NS, d);
        crate::diag::TRIAGE_NS_TOTAL.fetch_add(d, Ordering::SeqCst);
        r
    }

    fn lazy_triage_some_inner(&self, budget: usize) -> bool {
        let blocks: Vec<Block> = {
            let mut q = self.unswept_blocks.lock().unwrap();
            let n = q.len().min(budget);
            if n == 0 {
                self.unswept_nonempty.store(false, Ordering::Relaxed);
                return false;
            }
            let at = q.len() - n;
            let taken = q.split_off(at);
            if q.is_empty() {
                self.unswept_nonempty.store(false, Ordering::Relaxed);
            }
            taken
        };
        crate::diag::TRIAGE_CHUNKS.fetch_add(1, Ordering::SeqCst);
        let cur = self.line_mark_state.load(Ordering::Acquire);
        let unavail = self.line_unavail_state.load(Ordering::Acquire);
        // BISECT: idle-window only (during marking cur != unavail)
        if cur != unavail {
            self.unswept_blocks.lock().unwrap().append(&mut { blocks });
            self.unswept_nonempty.store(true, Ordering::Relaxed);
            return false;
        }
        // Batch dead-block releases: one accounting update and one global
        // queue-lock acquisition for the whole quantum, instead of a
        // singleton-queue allocation + write-lock per block.
        let mut dead: Vec<Block> = Vec::new();
        for block in blocks {
            debug_assert_ne!(block.get_state(), BlockState::Unallocated);
            let marked = block
                .lines()
                .filter(|l| l.is_marked(cur) || l.is_marked(unavail))
                .count();
            if marked == 0 {
                crate::diag::TRIAGE_FREED.fetch_add(1, Ordering::SeqCst);
                // DIAG QUARANTINE: leak dead blocks instead of freeing them
                // (MMTK_TRIAGE_QUARANTINE env) to discriminate "triage freed
                // a live block" from "someone scribbled on live memory".
                // Cached: getenv takes a process-wide libc lock and this runs
                // per dead block in the allocation slowpath.
                static QUARANTINE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
                if *QUARANTINE
                    .get_or_init(|| std::env::var_os("MMTK_TRIAGE_QUARANTINE").is_some())
                {
                    continue;
                }
                block.deinit();
                dead.push(block);
            } else if marked < Block::LINES {
                crate::diag::TRIAGE_POOLED.fetch_add(1, Ordering::SeqCst);
                block.set_state(BlockState::Reusable {
                    unavailable_lines: marked as _,
                });
                self.reusable_blocks.push(block);
            } else {
                block.set_state(BlockState::Marked);
                self.full_blocks.lock().unwrap().push(block);
            }
        }
        if !dead.is_empty() {
            self.pr.release_blocks_batch(&dead);
        }
        true
    }

    pub fn get_reusable_block(&self, copy: bool) -> Option<Block> {
        if super::BLOCK_ONLY {
            return None;
        }
        loop {
            let block = self.reusable_blocks.pop()?;

            // Skip blocks that should be evacuated.
            if copy && block.is_defrag_source() {
                continue;
            }

            // Get available lines. Do this before block.init which will reset block state.
            let lines_delta = match block.get_state() {
                BlockState::Reusable { unavailable_lines } => {
                    Block::LINES - unavailable_lines as usize
                }
                BlockState::Unmarked => Block::LINES,
                // Traced while pool-resident (marking is running): its hole
                // census is stale; send it back through the unswept pipeline.
                BlockState::Marked => {
                    self.pending_blocks.lock().unwrap().push(block);
                    continue;
                }
                _ => unreachable!("{:?} {:?}", block, block.get_state()),
            };
            self.lines_consumed.fetch_add(lines_delta, Ordering::SeqCst);
            self.nursery_lines_claimed
                .fetch_add(lines_delta, Ordering::Relaxed);

            block.init(copy);
            crate::diag::POOL_POPS.fetch_add(1, Ordering::SeqCst);
            return Some(block);
        }
    }

    /// Trace and mark objects without evacuation.
    pub fn trace_object_without_moving(
        &self,
        queue: &mut impl ObjectQueue,
        object: ObjectReference,
    ) -> ObjectReference {
        #[cfg(feature = "vo_bit")]
        vo_bit::helper::on_trace_object::<VM>(object);

        if self.attempt_mark(object, self.mark_state) {
            // Per-worker batched live-bytes accounting (pacer input): a
            // per-object fetch_add on the shared counter was a locked RMW
            // per marked object; the thread-local cell is flushed once per
            // work packet (see the worker loop), so the shared line sees
            // one RMW per ~thousands of objects and end_of_gc still reads
            // a complete total (workers only park between packets).
            LIVE_BYTES_TLS.with(|c| {
                c.set(
                    c.get()
                        + <VM::VMObjectModel as crate::vm::ObjectModel<VM>>::get_current_size(
                            object,
                        ),
                )
            });
            // Mark block and lines
            if !super::BLOCK_ONLY {
                if !super::MARK_LINE_AT_SCAN_TIME {
                    self.mark_lines(object);
                }
            } else {
                Block::containing(object).set_state(BlockState::Marked);
            }

            #[cfg(feature = "vo_bit")]
            vo_bit::helper::on_object_marked::<VM>(object);

            // Visit node
            queue.enqueue(object);
            self.unlog_object_if_needed(object);
            return object;
        }
        object
    }

    /// Trace object and do evacuation if required.
    #[allow(clippy::assertions_on_constants)]
    pub fn trace_object_with_opportunistic_copy(
        &self,
        queue: &mut impl ObjectQueue,
        object: ObjectReference,
        semantics: CopySemantics,
        worker: &mut GCWorker<VM>,
        nursery_collection: bool,
    ) -> ObjectReference {
        let copy_context = worker.get_copy_context_mut();
        debug_assert!(!super::BLOCK_ONLY);

        #[cfg(feature = "vo_bit")]
        vo_bit::helper::on_trace_object::<VM>(object);

        let forwarding_status = object_forwarding::attempt_to_forward::<VM>(object);
        if object_forwarding::state_is_forwarded_or_being_forwarded(forwarding_status) {
            // We lost the forwarding race as some other thread has set the forwarding word; wait
            // until the object has been forwarded by the winner. Note that the object may not
            // necessarily get forwarded since Immix opportunistically moves objects.
            #[allow(clippy::let_and_return)]
            let new_object =
                object_forwarding::spin_and_get_forwarded_object::<VM>(object, forwarding_status);
            #[cfg(debug_assertions)]
            {
                if new_object == object {
                    debug_assert!(
                        self.is_marked(object) || self.defrag.space_exhausted() || self.is_pinned(object),
                        "Forwarded object is the same as original object {} even though it should have been copied",
                        object,
                    );
                } else {
                    // new_object != object
                    debug_assert!(
                        !Block::containing(new_object).is_defrag_source(),
                        "Block {:?} containing forwarded object {} should not be a defragmentation source",
                        Block::containing(new_object),
                        new_object,
                    );
                }
            }
            new_object
        } else if self.is_marked(object) {
            // We won the forwarding race but the object is already marked so we clear the
            // forwarding status and return the unmoved object
            object_forwarding::clear_forwarding_bits::<VM>(object);
            object
        } else {
            // We won the forwarding race; actually forward and copy the object if it is not pinned
            // and we have sufficient space in our copy allocator
            let new_object = if self.is_pinned(object)
                || (!nursery_collection && self.defrag.space_exhausted())
            {
                if self.attempt_mark(object, self.mark_state) {
                    self.live_bytes.fetch_add(
                        <VM::VMObjectModel as crate::vm::ObjectModel<VM>>::get_current_size(object),
                        std::sync::atomic::Ordering::Relaxed,
                    );
                }
                object_forwarding::clear_forwarding_bits::<VM>(object);
                Block::containing(object).set_state(BlockState::Marked);

                #[cfg(feature = "vo_bit")]
                vo_bit::helper::on_object_marked::<VM>(object);

                if !super::MARK_LINE_AT_SCAN_TIME {
                    self.mark_lines(object);
                }

                self.unlog_object_if_needed(object);

                object
            } else {
                // We are forwarding objects. When the copy allocator allocates the block, it should
                // mark the block. So we do not need to explicitly mark it here.

                object_forwarding::forward_object::<VM>(
                    object,
                    semantics,
                    copy_context,
                    |new_object| {
                        // post_copy should have set the unlog bit
                        // if `unlog_traced_object` is true.
                        debug_assert!(
                            !self.common.unlog_traced_object
                                || VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                                    .is_unlogged::<VM>(new_object, Ordering::Relaxed)
                        );
                        #[cfg(feature = "vo_bit")]
                        vo_bit::helper::on_object_forwarded::<VM>(new_object);
                    },
                )
            };
            debug_assert_eq!(
                Block::containing(new_object).get_state(),
                BlockState::Marked
            );

            queue.enqueue(new_object);
            debug_assert!(new_object.is_live());
            new_object
        }
    }

    fn unlog_object_if_needed(&self, object: ObjectReference) {
        if self.common.unlog_traced_object {
            // Make sure the side metadata for the line can fit into one byte. For smaller line size, we should
            // use `mark_as_unlogged` instead to mark the bit.
            const_assert!(
                Line::BYTES
                    >= (1
                        << (crate::util::constants::LOG_BITS_IN_BYTE
                            + crate::util::constants::LOG_MIN_OBJECT_SIZE))
            );
            const_assert_eq!(
                crate::vm::object_model::specs::VMGlobalLogBitSpec::LOG_NUM_BITS,
                0
            ); // We should put this to the addition, but type casting is not allowed in constant assertions.

            // Every immix line is 256 bytes, which is mapped to 4 bytes in the side metadata.
            // If we have one object in the line that is mature, we can assume all the objects in the line are mature objects.
            // So we can just mark the byte.
            VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                .mark_byte_as_unlogged::<VM>(object, Ordering::Relaxed);
        }
    }

    /// Mark all the lines that the given object spans.
    #[allow(clippy::assertions_on_constants)]
    pub fn mark_lines(&self, object: ObjectReference) {
        debug_assert!(!super::BLOCK_ONLY);
        Line::mark_lines_for_object::<VM>(object, self.line_mark_state.load(Ordering::Acquire));
    }

    /// Atomically mark an object.
    fn attempt_mark(&self, object: ObjectReference, mark_state: u8) -> bool {
        loop {
            let old_value = VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.load_atomic::<VM, u8>(
                object,
                None,
                Ordering::SeqCst,
            );
            if old_value == mark_state {
                return false;
            }

            if VM::VMObjectModel::LOCAL_MARK_BIT_SPEC
                .compare_exchange_metadata::<VM, u8>(
                    object,
                    old_value,
                    mark_state,
                    None,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                )
                .is_ok()
            {
                break;
            }
        }
        true
    }

    /// Check if an object is marked.
    fn is_marked_with(&self, object: ObjectReference, mark_state: u8) -> bool {
        let old_value = VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.load_atomic::<VM, u8>(
            object,
            None,
            Ordering::SeqCst,
        );
        old_value == mark_state
    }

    pub(crate) fn is_marked(&self, object: ObjectReference) -> bool {
        self.is_marked_with(object, self.mark_state)
    }

    /// Check if an object is pinned.
    fn is_pinned(&self, _object: ObjectReference) -> bool {
        #[cfg(feature = "object_pinning")]
        return self.is_object_pinned(_object);

        #[cfg(not(feature = "object_pinning"))]
        false
    }

    /// Hole searching.
    ///
    /// Linearly scan lines in a block to search for the next
    /// hole, starting from the given line. If we find available lines,
    /// return a tuple of the start line and the end line (non-inclusive).
    ///
    /// Returns None if the search could not find any more holes.
    #[allow(clippy::assertions_on_constants)]
    pub fn get_next_available_lines(&self, search_start: Line) -> Option<(Line, Line)> {
        debug_assert!(!super::BLOCK_ONLY);
        let unavail_state = self.line_unavail_state.load(Ordering::Acquire);
        let current_state = self.line_mark_state.load(Ordering::Acquire);
        let block = search_start.block();
        let mark_data = block.line_mark_table();
        let start_cursor = search_start.get_index_within_block();
        let mut cursor = start_cursor;
        // Find start
        while cursor < mark_data.len() {
            let mark = mark_data.get(cursor);
            if mark != unavail_state && mark != current_state && mark != Line::CLAIMED_MARK_STATE {
                break;
            }
            cursor += 1;
        }
        if cursor == mark_data.len() {
            return None;
        }
        let start = search_start.next_nth(cursor - start_cursor);
        // Find limit
        while cursor < mark_data.len() {
            let mark = mark_data.get(cursor);
            if mark == unavail_state || mark == current_state || mark == Line::CLAIMED_MARK_STATE {
                break;
            }
            cursor += 1;
        }
        let end = search_start.next_nth(cursor - start_cursor);
        debug_assert!(RegionIterator::<Line>::new(start, end).all(|line| !line
            .is_marked(unavail_state)
            && !line.is_marked(current_state)
            && !line.is_marked(Line::CLAIMED_MARK_STATE)));
        Some((start, end))
    }

    pub fn is_last_gc_exhaustive(&self, did_defrag_for_last_gc: bool) -> bool {
        if self.is_defrag_enabled() {
            did_defrag_for_last_gc
        } else {
            // If defrag is disabled, every GC is exhaustive.
            true
        }
    }

    pub(crate) fn get_pages_allocated(&self) -> usize {
        self.lines_consumed.load(Ordering::SeqCst) >> (LOG_BYTES_IN_PAGE - Line::LOG_BYTES as u8)
    }

    /// Post copy routine for Immix copy contexts
    fn post_copy(&self, object: ObjectReference, _bytes: usize) {
        // Mark the object
        VM::VMObjectModel::LOCAL_MARK_BIT_SPEC.store_atomic::<VM, u8>(
            object,
            self.mark_state,
            None,
            Ordering::SeqCst,
        );
        // Mark the line
        if !super::MARK_LINE_AT_SCAN_TIME {
            self.mark_lines(object);
        }
        if self.common.unlog_traced_object {
            VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC
                .mark_byte_as_unlogged::<VM>(object, Ordering::Relaxed);
        }
    }

    pub(crate) fn prefer_copy_on_nursery_gc(&self) -> bool {
        self.is_nursery_copy_enabled()
    }

    pub(crate) fn is_nursery_copy_enabled(&self) -> bool {
        !self.space_args.never_move_objects && !cfg!(feature = "sticky_immix_non_moving_nursery")
    }

    pub(crate) fn is_defrag_enabled(&self) -> bool {
        !self.space_args.never_move_objects
    }
}

/// A work packet to prepare each block for a major GC.
/// Performs the action on a range of chunks.
pub struct PrepareBlockState<VM: VMBinding> {
    #[allow(dead_code)]
    pub space: &'static ImmixSpace<VM>,
    pub chunk: Chunk,
    pub defrag_threshold: Option<usize>,
    pub unlog_bits_op: UnlogBitsOperation,
}

impl<VM: VMBinding> PrepareBlockState<VM> {
    /// Clear object mark table
    fn reset_object_mark(&self) {
        // NOTE: We reset the mark bits because cyclic mark bit is currently not supported, yet.
        // See `ImmixSpace::prepare`.
        if let MetadataSpec::OnSide(side) = *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC {
            side.bzero_metadata(self.chunk.start(), Chunk::BYTES);
        }
    }
}

impl<VM: VMBinding> GCWork<VM> for PrepareBlockState<VM> {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, mmtk: &'static MMTK<VM>) {
        // Clear object mark table for this chunk
        self.reset_object_mark();
        // Iterate over all blocks in this chunk
        for block in self.chunk.iter_region::<Block>() {
            let state = block.get_state();
            // Skip unallocated blocks.
            if state == BlockState::Unallocated {
                continue;
            }
            // Check if this block needs to be defragmented.
            let is_defrag_source = if !self.space.is_defrag_enabled() {
                // Do not set any block as defrag source if defrag is disabled.
                false
            } else if *mmtk.options.immix_defrag_every_block {
                // Set every block as defrag source if so desired.
                true
            } else if let Some(defrag_threshold) = self.defrag_threshold {
                // This GC is a defrag GC.
                block.get_holes() > defrag_threshold
            } else {
                // Not a defrag GC.
                false
            };
            block.set_as_defrag_source(is_defrag_source);
            // Clear block mark data.
            block.set_state(BlockState::Unmarked);
            debug_assert!(!block.get_state().is_reusable());
            debug_assert_ne!(block.get_state(), BlockState::Marked);
        }

        self.unlog_bits_op
            .execute::<VM>(self.chunk.start(), Chunk::BYTES);
    }
}

/// Chunk sweeping work packet.
struct SweepTimer(u64);
impl Drop for SweepTimer {
    fn drop(&mut self) {
        let d = crate::diag::now_ns().saturating_sub(self.0);
        crate::diag::SWEEP_NS.fetch_add(d, std::sync::atomic::Ordering::Relaxed);
        crate::diag::SWEEP_PKTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        crate::diag::SWEEP_OUTSTANDING
            .fetch_update(std::sync::atomic::Ordering::SeqCst,
                          std::sync::atomic::Ordering::SeqCst,
                          |v| Some(v.saturating_sub(1)))
            .ok();
    }
}

/// LEG 1: deferred per-chunk object-mark-bit clear (the work
/// `PrepareBlockState::reset_object_mark` used to do inside the InitialMark
/// pause).  Runs concurrently after FinalMark; mark bits are unread between
/// cycles and mutators never write them.
/// In-pause parallel nursery census (see `sweep_nursery_blocks`).
struct CensusNurseryBlocks<VM: VMBinding> {
    space: &'static ImmixSpace<VM>,
    blocks: Vec<Block>,
}

impl<VM: VMBinding> GCWork<VM> for CensusNurseryBlocks<VM> {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, _mmtk: &'static MMTK<VM>) {
        self.space
            .census_nursery_blocks(std::mem::take(&mut self.blocks));
    }
}

struct ClearChunkMarks<VM: VMBinding> {
    chunk: Chunk,
    _p: std::marker::PhantomData<VM>,
}

impl<VM: VMBinding> GCWork<VM> for ClearChunkMarks<VM> {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, _mmtk: &'static MMTK<VM>) {
        if let MetadataSpec::OnSide(side) = *VM::VMObjectModel::LOCAL_MARK_BIT_SPEC {
            side.bzero_metadata(self.chunk.start(), Chunk::BYTES);
        }
    }
}

/// Parallel per-chunk unlog-bit maintenance for lazy sweeping.
struct UnlogBitsChunk<VM: VMBinding> {
    space: &'static ImmixSpace<VM>,
    chunk: Chunk,
    op: UnlogBitsOperation,
}

impl<VM: VMBinding> GCWork<VM> for UnlogBitsChunk<VM> {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, _mmtk: &'static MMTK<VM>) {
        let _ = self.space;
        let log_bit = VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.extract_side_spec();
        match self.op {
            UnlogBitsOperation::BulkClear => log_bit.bzero_metadata(self.chunk.start(), Chunk::BYTES),
            UnlogBitsOperation::BulkSet => log_bit.bset_metadata(self.chunk.start(), Chunk::BYTES),
            UnlogBitsOperation::NoOp => {}
        }
    }
}

struct SweepChunk<VM: VMBinding> {
    /// FIX E: metadata-only triage instead of full sweep (lazy sweeping).
    lazy: bool,
    space: &'static ImmixSpace<VM>,
    chunk: Chunk,
    unlog_bits_op: UnlogBitsOperation,
    /// A destructor invoked when all `SweepChunk` packets are finished.
    epilogue: Arc<FlushPageResource<VM>>,
}

impl<VM: VMBinding> GCWork<VM> for SweepChunk<VM> {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, mmtk: &'static MMTK<VM>) {
        let __sweep_t0 = crate::diag::now_ns();
        let __sweep_guard = SweepTimer(__sweep_t0);
        assert!(self.space.chunk_map.get(self.chunk).unwrap().is_allocated());

        if self.lazy {
            let lstate = self.space.line_mark_state.load(Ordering::Acquire);
            for block in self
                .chunk
                .iter_region::<Block>()
                .filter(|b| b.get_state() != BlockState::Unallocated)
            {
                // Liveness by LINE marks: allocate-black marks lines, not block state.
                if block.lines().any(|l| l.is_marked(lstate)) {
                    #[cfg(feature = "vo_bit")]
                    crate::util::metadata::vo_bit::helper::on_region_swept::<VM, _>(&block, true);
                    block.set_state(BlockState::Reusable { unavailable_lines: 1 });
                    self.space.reusable_blocks.push(block);
                } else {
                    #[cfg(feature = "vo_bit")]
                    crate::util::metadata::vo_bit::helper::on_region_swept::<VM, _>(&block, false);
                    self.space.release_block(block);
                }
            }
            self.epilogue.finish_one_work_packet();
            return;
        }

        let mut histogram = self.space.defrag.new_histogram();
        let line_mark_state = if super::BLOCK_ONLY {
            None
        } else {
            Some(self.space.line_mark_state.load(Ordering::Acquire))
        };
        // Hints for clearing side forwarding bits.
        let is_moving_gc = mmtk.get_plan().current_gc_may_move_object();
        let is_defrag_gc = self.space.defrag.in_defrag();

        // number of swept (completely free) blocks.
        let mut swept_blocks = 0;
        // number of reused blocks.
        let mut reused_blocks = 0;
        // number of non-free blocks that cannot be reused (e.g. full, or non-empty when block-only).
        let mut unreused_blocks = 0;

        // Iterate over all allocated blocks in this chunk.
        for block in self
            .chunk
            .iter_region::<Block>()
            .filter(|block| block.get_state() != BlockState::Unallocated)
        {
            // Clear side forwarding bits.
            // In the beginning of the next GC, no side forwarding bits shall be set.
            // In this way, we can omit clearing forwarding bits when copying object.
            // See `GCWorkerCopyContext::post_copy`.
            // Note, `block.sweep()` overwrites `DEFRAG_STATE_TABLE` with the number of holes,
            // but we need it to know if a block is a defrag source.
            // We clear forwarding bits before `block.sweep()`.
            if let MetadataSpec::OnSide(side) = *VM::VMObjectModel::LOCAL_FORWARDING_BITS_SPEC {
                if is_moving_gc {
                    let objects_may_move = if is_defrag_gc {
                        // If it is a defrag GC, we only clear forwarding bits for defrag sources.
                        block.is_defrag_source()
                    } else {
                        // Otherwise, it must be a nursery GC of StickyImmix with copying nursery.
                        // We don't have information about which block contains moved objects,
                        // so we have to clear forwarding bits for all blocks.
                        true
                    };
                    if objects_may_move {
                        side.bzero_metadata(block.start(), Block::BYTES);
                    }
                }
            }

            match block.sweep(self.space, &mut histogram, line_mark_state) {
                BlockSweepResult::Swept => swept_blocks += 1,
                BlockSweepResult::Reused => reused_blocks += 1,
                BlockSweepResult::NoReuse => unreused_blocks += 1,
            }
        }

        probe!(
            mmtk,
            sweep_chunk_immix,
            swept_blocks,
            reused_blocks,
            unreused_blocks
        );

        // number of allocated blocks.
        let allocated_blocks = reused_blocks + unreused_blocks;

        // Set this chunk as free if there is not live blocks.
        if allocated_blocks == 0 {
            self.space.chunk_map.set_allocated(self.chunk, false)
        }
        self.space.defrag.add_completed_mark_histogram(histogram);

        self.unlog_bits_op
            .execute::<VM>(self.chunk.start(), Chunk::BYTES);

        self.epilogue.finish_one_work_packet();
    }
}

/// Count number of remaining work pacets, and flush page resource if all packets are finished.
struct FlushPageResource<VM: VMBinding> {
    space: &'static ImmixSpace<VM>,
    counter: AtomicUsize,
}

impl<VM: VMBinding> FlushPageResource<VM> {
    /// Called after a related work packet is finished.
    fn finish_one_work_packet(&self) {
        if 1 == self.counter.fetch_sub(1, Ordering::SeqCst) {
            // We've finished releasing all the dead blocks to the BlockPageResource's thread-local queues.
            // Now flush the BlockPageResource.
            self.space.flush_page_resource()
        }
    }
}

impl<VM: VMBinding> Drop for FlushPageResource<VM> {
    fn drop(&mut self) {
        epilogue::debug_assert_counter_zero(&self.counter, "FlushPageResource::counter");
    }
}

use crate::policy::copy_context::PolicyCopyContext;
use crate::util::alloc::Allocator;
use crate::util::alloc::ImmixAllocator;

/// Normal immix copy context. It has one copying Immix allocator.
/// Most immix plans use this copy context.
pub struct ImmixCopyContext<VM: VMBinding> {
    allocator: ImmixAllocator<VM>,
}

impl<VM: VMBinding> PolicyCopyContext for ImmixCopyContext<VM> {
    type VM = VM;

    fn prepare(&mut self) {
        self.allocator.reset();
    }
    fn release(&mut self) {
        self.allocator.reset();
    }
    fn alloc_copy(
        &mut self,
        _original: ObjectReference,
        bytes: usize,
        align: usize,
        offset: usize,
    ) -> Address {
        self.allocator.alloc(bytes, align, offset)
    }
    fn post_copy(&mut self, obj: ObjectReference, bytes: usize) {
        self.get_space().post_copy(obj, bytes)
    }
}

impl<VM: VMBinding> ImmixCopyContext<VM> {
    pub(crate) fn new(
        tls: VMWorkerThread,
        context: Arc<AllocatorContext<VM>>,
        space: &'static ImmixSpace<VM>,
    ) -> Self {
        ImmixCopyContext {
            allocator: ImmixAllocator::new(tls.0, Some(space), context, true),
        }
    }

    fn get_space(&self) -> &ImmixSpace<VM> {
        self.allocator.immix_space()
    }
}

/// Hybrid Immix copy context. It includes two different immix allocators. One with `copy = true`
/// is used for defrag GCs, and the other is used for other purposes (such as promoting objects from
/// nursery to Immix mature space). This is used by generational immix.
pub struct ImmixHybridCopyContext<VM: VMBinding> {
    copy_allocator: ImmixAllocator<VM>,
    defrag_allocator: ImmixAllocator<VM>,
}

impl<VM: VMBinding> PolicyCopyContext for ImmixHybridCopyContext<VM> {
    type VM = VM;

    fn prepare(&mut self) {
        self.copy_allocator.reset();
        self.defrag_allocator.reset();
    }
    fn release(&mut self) {
        self.copy_allocator.reset();
        self.defrag_allocator.reset();
    }
    fn alloc_copy(
        &mut self,
        _original: ObjectReference,
        bytes: usize,
        align: usize,
        offset: usize,
    ) -> Address {
        if self.get_space().in_defrag() {
            self.defrag_allocator.alloc(bytes, align, offset)
        } else {
            self.copy_allocator.alloc(bytes, align, offset)
        }
    }
    fn post_copy(&mut self, obj: ObjectReference, bytes: usize) {
        self.get_space().post_copy(obj, bytes)
    }
}

impl<VM: VMBinding> ImmixHybridCopyContext<VM> {
    pub(crate) fn new(
        tls: VMWorkerThread,
        context: Arc<AllocatorContext<VM>>,
        space: &'static ImmixSpace<VM>,
    ) -> Self {
        ImmixHybridCopyContext {
            copy_allocator: ImmixAllocator::new(tls.0, Some(space), context.clone(), false),
            defrag_allocator: ImmixAllocator::new(tls.0, Some(space), context, true),
        }
    }

    fn get_space(&self) -> &ImmixSpace<VM> {
        // Both copy allocators should point to the same space.
        debug_assert_eq!(
            self.defrag_allocator.immix_space().common().descriptor,
            self.copy_allocator.immix_space().common().descriptor
        );
        // Just get the space from either allocator
        self.defrag_allocator.immix_space()
    }
}

#[cfg(feature = "vo_bit")]
#[derive(Clone, Copy)]
enum VOBitsClearingScope {
    /// Clear all VO bits in all blocks.
    FullGC,
    /// Clear unmarked blocks, only.
    BlockOnly,
    /// Clear unmarked lines, only.  (i.e. lines with line mark state **not** equal to `state`).
    Line { state: u8 },
}

/// A work packet to clear VO bit metadata after Prepare.
#[cfg(feature = "vo_bit")]
struct ClearVOBitsAfterPrepare {
    chunk: Chunk,
    scope: VOBitsClearingScope,
}

#[cfg(feature = "vo_bit")]
impl<VM: VMBinding> GCWork<VM> for ClearVOBitsAfterPrepare {
    fn do_work(&mut self, _worker: &mut GCWorker<VM>, _mmtk: &'static MMTK<VM>) {
        match self.scope {
            VOBitsClearingScope::FullGC => {
                vo_bit::bzero_vo_bit(self.chunk.start(), Chunk::BYTES);
            }
            VOBitsClearingScope::BlockOnly => {
                self.clear_blocks(None);
            }
            VOBitsClearingScope::Line { state } => {
                self.clear_blocks(Some(state));
            }
        }
    }
}

#[cfg(feature = "vo_bit")]
impl ClearVOBitsAfterPrepare {
    fn clear_blocks(&mut self, line_mark_state: Option<u8>) {
        for block in self
            .chunk
            .iter_region::<Block>()
            .filter(|block| block.get_state() != BlockState::Unallocated)
        {
            block.clear_vo_bits_for_unmarked_regions(line_mark_state);
        }
    }
}
