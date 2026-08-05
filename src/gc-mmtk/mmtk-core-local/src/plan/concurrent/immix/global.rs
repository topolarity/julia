use crate::plan::concurrent::global::ConcurrentPlan;
use crate::plan::concurrent::immix::gc_work::ConcurrentImmixGCWorkContext;
use crate::plan::concurrent::immix::gc_work::ConcurrentImmixSTWGCWorkContext;
use crate::plan::concurrent::Pause;
use crate::plan::global::BasePlan;
use crate::plan::global::CommonPlan;
use crate::plan::global::CreateGeneralPlanArgs;
use crate::plan::global::CreateSpecificPlanArgs;
use crate::plan::immix::mutator::ALLOCATOR_MAPPING;
use crate::plan::tracing::gc_work::weakref::VMProcessWeakRefs;
use crate::plan::AllocationSemantics;
use crate::plan::Plan;
use crate::plan::PlanConstraints;
use crate::policy::gc_work::TraceKind;
use crate::policy::immix::defrag::StatsForDefrag;
use crate::policy::immix::ImmixSpaceArgs;
use crate::policy::immix::TRACE_KIND_DEFRAG;
use crate::policy::immix::TRACE_KIND_FAST;
use crate::policy::space::Space;
use crate::scheduler::gc_work::Release;
use crate::scheduler::gc_work::StopMutators;
use crate::scheduler::*;
use crate::util::alloc::allocators::AllocatorSelector;
use crate::util::copy::*;
use crate::util::heap::gc_trigger::SpaceStats;
use crate::util::heap::VMRequest;
use crate::util::metadata::log_bit::UnlogBitsOperation;
use crate::util::metadata::side_metadata::SideMetadataContext;
use crate::vm::ObjectModel;
use crate::vm::Collection;
use crate::vm::VMBinding;
use crate::util::ObjectReference;
use crate::{policy::immix::ImmixSpace, util::opaque_pointer::VMWorkerThread};
use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicU64;

use atomic::Atomic;
use atomic::Ordering;
use enum_map::EnumMap;

use mmtk_macros::{HasSpaces, PlanTraceObject};

/// A concurrent Immix plan. The plan supports concurrent collection (strictly non-moving) and STW full heap collection (which may do defrag).
/// The concurrent GC consists of two STW pauses (initial mark and final mark) with concurrent marking in between.
#[derive(HasSpaces, PlanTraceObject)]
pub struct ConcurrentImmix<VM: VMBinding> {
    #[post_scan]
    #[space]
    #[copy_semantics(CopySemantics::DefaultCopy)]
    pub immix_space: ImmixSpace<VM>,
    #[parent]
    pub common: CommonPlan<VM>,
    last_gc_was_defrag: AtomicBool,
    current_pause: Atomic<Option<Pause>>,
    previous_pause: Atomic<Option<Pause>>,
    should_do_full_gc: AtomicBool,
    concurrent_marking_active: AtomicBool,
    // FIX A (pacing): start marking from predicted exhaustion rather than a fixed fraction of the
    // heap.  Interacts with FIX C: the head start is what makes the hastened FinalMark cheap,
    // because marking is nearly done by the time the heap trigger fires.
    mark_start_ns: AtomicU64,
    mark_dur_ns: AtomicU64,
    gc_end_ns: AtomicU64,
    /// ALWAYS-ON BARRIER: remembered set accumulated between collections (old
    /// objects mutated while no marking is active; flushed here from the
    /// per-mutator barrier buffers).  Drained inside every pause: minors scan
    /// the entries for old->young edges; InitialMark/Full re-arm them (a
    /// major traces everything reachable anyway).
    remset: std::sync::Mutex<Vec<ObjectReference>>,
    /// GENERATIONAL TRIGGER: which collection kind the last trigger request
    /// asked for.  Set by `collection_required`, consumed by
    /// `schedule_collection`; a major request wins over a minor one.
    minor_due: AtomicBool,
    major_due: AtomicBool,
    /// RAGGED PRE-FLUSH state: epoch counter (0 = no round open), ack
    /// count, and round start time for the timeout (mutators that never
    /// poll -- non-allocating loops -- must not stall the FinalMark; the
    /// in-pause flush plus detect-and-abort backstop covers them).
    ragged_epoch: std::sync::atomic::AtomicUsize,
    ragged_acks: std::sync::atomic::AtomicUsize,
    ragged_start_ns: AtomicU64,
    /// GO-STYLE TERMINATION: set when a FinalMark pause found over-budget
    /// SATB work at the flush and aborted (marking continues; the pause's
    /// release/ref stages no-op; the next pause retries FinalMark).
    final_mark_aborted: AtomicBool,
    /// EXTERNAL-QUANTA PRESSURE: snapshots of counted-malloc (vm_live_bytes)
    /// and LOS reserved pages at the last collection.  The nursery trigger
    /// only counted immix claimed lines, so workloads whose allocation is
    /// dominated by malloc'd memory (BigInt limbs via counted_malloc) or
    /// large objects never fired minors: reclamation became major-only,
    /// majors are paced by heap size, heap size includes the unreclaimed
    /// float -- a feedback loop that grew the heap without bound
    /// (pidigits: RSS past 80 GB).  Growth since these snapshots now counts
    /// toward the nursery threshold, so external pressure drives frequent
    /// cheap minors (whose finalizer sweep is what frees malloc'd memory),
    /// matching the stock GC's malloc-driven young-collection cadence.
    malloc_pages_at_last_gc: std::sync::atomic::AtomicUsize,
    los_pages_at_last_gc: std::sync::atomic::AtomicUsize,
}

/// The plan constraints for the concurrent immix plan.
pub const CONCURRENT_IMMIX_CONSTRAINTS: PlanConstraints = PlanConstraints {
    // If we disable moving in Immix, this is a non-moving plan.
    moves_objects: !cfg!(feature = "immix_non_moving"),
    // Max immix object size is half of a block.
    max_non_los_default_alloc_bytes: crate::policy::immix::MAX_IMMIX_OBJECT_SIZE,
    needs_prepare_mutator: true,
    barrier: crate::BarrierSelector::SATBBarrier,
    needs_log_bit: true,
    ..PlanConstraints::default()
};

impl<VM: VMBinding> Plan for ConcurrentImmix<VM> {
    fn collection_required(&self, space_full: bool, _space: Option<SpaceStats<Self::VM>>) -> bool {
        // FLOAT-BUDGET TRIGGER.  Under fully-deferred lazy sweeping, reserved
        // pages carry no information: blocks cycle old -> triage -> reuse and
        // the heap always looks full.  The trigger therefore runs on the
        // current cycle's float (blocks acquired since the last FinalMark,
        // tracked exactly by `pending_blocks`): start marking when it exceeds
        // (total - live)/3, giving the steady state young <= H/3, old <= H/3,
        // and H/3 of slack for the drain to supply allocation.
        // ASYNC TRIGGER (request-and-continue): returning `true` from this
        // method makes the poll chain block the allocating mutator in
        // `block_for_gc` for the whole request->rendezvous->pause window.
        // That is only justified when the allocation genuinely cannot
        // proceed (`space_full`, or exhaustion with nothing left to drain).
        // Advisory triggers -- the float budget and reserve-pressure
        // hastening -- instead request the cycle directly on the scheduler
        // (`gc_trigger.request()`) and return `false`: the allocation is
        // satisfied from the guaranteed headroom and the mutator is stopped
        // later by the pause safepoint, paying only the true pause.
        let marking = self.concurrent_marking_in_progress();
        // MINOR TRIGGER -- checked FIRST on advisory polls.  It must not sit
        // behind the base heap-full branch: a heap running over its goal
        // (large malloc/LOS float) takes that branch on every poll and its
        // backlog-suppress path returns early, which starved minors exactly
        // when external pressure made them most necessary (pidigits: one
        // minor in 45s, reclamation went major-only, the float fed back
        // into the goal).  Real walls (space_full) still take the blocking
        // paths below.
        if !space_full && !marking && Self::nursery_threshold_pages() != 0 {
            let total = self.get_total_pages();
            let live = self.immix_space.live_prev_pages();
            let scaled = total.saturating_sub(live) / 6;
            let threshold = Self::nursery_threshold_pages()
                .min(scaled)
                .max(1024 /* 4 MB floor */);
            // External quanta count toward the nursery: counted-malloc
            // growth (net vm_live_bytes since the last collection) and LOS
            // growth.  See the snapshot fields for the rationale.
            let malloc_pages = crate::util::conversions::bytes_to_pages_up(
                <VM as VMBinding>::VMCollection::vm_live_bytes(),
            )
            .saturating_sub(self.malloc_pages_at_last_gc.load(Ordering::Relaxed));
            let los_pages = self
                .common
                .get_los()
                .reserved_pages()
                .saturating_sub(self.los_pages_at_last_gc.load(Ordering::Relaxed));
            if self.immix_space.nursery_claimed_pages() + malloc_pages + los_pages >= threshold {
                self.minor_due.store(true, Ordering::Release);
                crate::diag::PACER_REQ_MINOR.fetch_add(1, Ordering::Relaxed);
                self.base().gc_trigger.request();
                return false;
            }
        }
        if self.base().collection_required(self, space_full) {
            // FIX C: a running cycle is never abandoned -- hasten FinalMark.
            if marking {
                if space_full {
                    // The allocation actually failed: real wall, block.
                    if crate::diag::pacer_trace_enabled() {
                        eprintln!("[pacer-block] space_full during marking: hasten FinalMark (blocking)");
                    }
                    return true;
                }
                // Advisory pressure during marking: do NOT request the
                // FinalMark from here.  The pause cannot legitimately
                // complete before the concurrent drain finishes, so an
                // early request only bypasses the ragged pre-flush and
                // races the drain -- the flushed work (e.g. a logged
                // array's transitive scan) then lands inside the pause
                // (measured: 370-410ms FinalMarks).  The all-parked
                // self-trigger requests the pause the moment the drain is
                // actually complete; allocation proceeds from headroom
                // meanwhile.
                info!("Heap trigger during concurrent marking: deferring to drained self-trigger");
                return false;
            }
            // Reserved-based pressure while aged reclaimable memory exists is
            // not real pressure: a failed acquisition falls through to the
            // allocator drain loop.  Suppress -- but ONLY for advisory polls.
            // On a real allocation failure (`space_full`) the caller parks in
            // `block_for_gc` unconditionally, so suppressing here would park
            // the mutator with no collection in flight (deadlock).
            if space_full {
                // Real wall.  With reclaimable supply left, a (blocking)
                // concurrent cycle plus the allocator drain loop recovers;
                // with the aged generation empty this is genuine exhaustion.
                if self.immix_space.has_unswept() || self.immix_space.has_reusable() {
                    if crate::diag::pacer_trace_enabled() {
                        eprintln!("[pacer-block] space_full with reclaimable supply: start cycle (blocking)");
                    }
                    return true;
                }
                self.should_do_full_gc.store(true, Ordering::Release);
                if crate::diag::pacer_trace_enabled() {
                    eprintln!("[pacer-block] genuine exhaustion: full GC (blocking)");
                }
                return true;
            }
            // Advisory poll while over the reserve goal: reserved pages
            // carry no information under deferred release (the goal never
            // accounts for the fragmentation floor, so resv > goal is the
            // steady state -- measured: this branch alone requested every
            // cycle, 26 back-to-back on strings, before the promotion and
            // float budgets below ever fired).  Fall through and let those
            // byte-accurate budgets decide.
        }

        if self.concurrent_marking_is_disabled() || marking {
            return false;
        }

        let total = self.get_total_pages();

        // MINOR TRIGGER: checked before the major advisories -- minors have
        // first claim on the allocation float (it IS the nursery), and each
        // minor resets it, so the float-budget major below stops firing once
        // minors run.  Majors then come from the pacing/goal path, driven by
        // genuine old-generation growth.  The threshold stays under the
        // major float budget (else majors always preempt) and is capped at
        // cache scale.  Minors are forbidden while marking (`!marking`
        // guards this branch); during a major cycle the nursery just grows
        // and the FinalMark-hastening path bounds the wait.
        // OLD-GROWTH TRIGGER: with minors absorbing the allocation float,
        // only a major reclaims promoted garbage.  Reserved pages are no
        // signal under lazy sweep (backlog-inflated right after a major);
        // the exact promotion volume is the live_bytes delta (each minor's
        // successful first marks).  Request a major once promotion since
        // the last major exceeds max(live estimate, 64 MB capped at a
        // quarter of the heap) -- GOGC-style 100% growth with a floor.
        // Checked before the minor branch: a major subsumes the minor.
        {
            let promoted_pages = self.immix_space.promoted_bytes_since_major() >> 12;
            let live = self.immix_space.live_prev_pages();
            let threshold = live.max(16384usize.min(total / 4).max(1024));
            if promoted_pages >= threshold {
                self.major_due.store(true, Ordering::Release);
                crate::diag::PACER_REQ_PROMO.fetch_add(1, Ordering::Relaxed);
                self.base().gc_trigger.request();
                return false;
            }
        }


        // PACING TRIGGER (Go-pacer style): the trigger policy publishes how
        // many pages of allocation a full concurrent cycle must ride out
        // (`alloc_rate x cycle_duration x margin`, measured in-system).
        // Request the next cycle while at least that much headroom remains
        // below the target, so the cycle finishes before allocation reaches
        // the blocking wall (`is_heap_full`).  Advisory: never blocks.
        // START-EARLY pacing on unpolluted inputs: committed = live estimate
        // (incl. minor promotion) + current byte-accurate float.  `reserved`
        // is NOT usable here -- the fragmentation floor inflates it (strings:
        // resv 2.5GB vs live 480MB), and the resv-based check cycled
        // back-to-back for zero reclaim.  But a workload whose LIVE genuinely
        // grows toward the goal (list) must start cycles ahead of the
        // `is_heap_full` wall or every wall blocks for a full cycle
        // (measured: 30 x ~300ms = 9.2s of blocking on list without this).
        if let Some(headroom) = self.base().gc_trigger.policy.concurrent_headroom_pages() {
            let committed = self.immix_space.live_now_pages() + self.immix_space.float_pages();
            if committed + headroom >= total {
                info!(
                    "Pacing trigger: committed {committed} + cycle headroom {headroom} >= target {total} pages: request concurrent marking (async)"
                );
                self.major_due.store(true, Ordering::Release);
                crate::diag::PACER_REQ_HEADROOM.fetch_add(1, Ordering::Relaxed);
                self.base().gc_trigger.request();
                return false;
            }
        }

        let live = self
            .immix_space
            .live_prev_pages();
        // Live-proportional (GOGC-style) float budget: spare heap LIMIT is
        // OOM headroom, not license for bigger cycles (measured: a
        // limit-proportional budget makes pause scale with the limit).
        const FLOAT_FLOOR_PAGES: usize = 32768; // 128 MB
        let budget = live
            .max(FLOAT_FLOOR_PAGES)
            .min(total.saturating_sub(live) / 3);
        if self.immix_space.float_pages() > budget {
            // Advisory by construction: budget <= (total - live)/3, so there
            // is always headroom to satisfy this allocation.  Never block.
            info!("Float exceeds budget ({budget} pages): request concurrent marking (async)");
            self.major_due.store(true, Ordering::Release);
            crate::diag::PACER_REQ_FLOAT.fetch_add(1, Ordering::Relaxed);
            self.base().gc_trigger.request();
            return false;
        }

        false
    }

    fn last_collection_was_exhaustive(&self) -> bool {
        self.immix_space
            .is_last_gc_exhaustive(self.last_gc_was_defrag.load(Ordering::Relaxed))
    }

    /// InitialMark/FinalMark never copy (allocate-black SATB, no evacuation),
    /// so the per-worker copy-context reset packets are pure wake-edge cost.
    /// Keep them for Full, which may defrag.
    fn needs_collector_context_packets(&self) -> bool {
        match self.current_pause() {
            Some(Pause::InitialMark) | Some(Pause::FinalMark) | Some(Pause::Nursery) => false,
            _ => true,
        }
    }

    fn constraints(&self) -> &'static PlanConstraints {
        &CONCURRENT_IMMIX_CONSTRAINTS
    }

    fn create_copy_config(&'static self) -> CopyConfig<Self::VM> {
        use enum_map::enum_map;
        CopyConfig {
            copy_mapping: enum_map! {
                CopySemantics::DefaultCopy => CopySelector::Immix(0),
                _ => CopySelector::Unused,
            },
            space_mapping: vec![(CopySelector::Immix(0), &self.immix_space)],
            constraints: &CONCURRENT_IMMIX_CONSTRAINTS,
        }
    }

    fn schedule_collection(&'static self, scheduler: &GCWorkScheduler<VM>) {
        // If concurrent marking is disabled, force a full GC.
        // Though we have checked in collection_required to not trigger a concurrent GC, it is still possible
        // that a GC is triggered without going through collection_required, e.g. a user triggered GC, or a GC trigger
        // implemented at the binding side without calling collection_required.
        // In those cases, we also want to force a full GC.
        if self.concurrent_marking_is_disabled() {
            self.should_do_full_gc.store(true, Ordering::SeqCst);
        }

        self.final_mark_aborted.store(false, Ordering::SeqCst);
        let minor_due = self.minor_due.swap(false, Ordering::SeqCst);
        let major_due = self.major_due.swap(false, Ordering::SeqCst);
        let pause = if self.concurrent_marking_in_progress() {
            // FIXME: Currently it is unsafe to bypass `FinalMark` and go directly from `InitialMark` to `Full`.
            // It is related to defragmentation.  See https://github.com/mmtk/mmtk-core/issues/1357 for more details.
            // We currently force `FinalMark` to happen if the last pause is `InitialMark`.
            Pause::FinalMark
        } else if self.should_do_full_gc.load(Ordering::SeqCst)
            // For user-triggered GCs, we don't want a simple initial pause which reclaims nothing.
            // We do a full STW collection for user triggered collection instead.
            || self.base().global_state.is_user_triggered_collection()
        {
            Pause::Full
        } else if minor_due && !major_due {
            // GENERATIONAL: nursery-threshold request, with no major
            // condition outstanding.  A major request wins when both fired
            // in the same window (it subsumes the minor).
            Pause::Nursery
        } else {
            Pause::InitialMark
        };

        self.current_pause.store(Some(pause), Ordering::SeqCst);

        probe!(mmtk, concurrent_pause_determined, pause as usize);

        match pause {
            Pause::Full => {
                // Ref closure buckets is disabled by initial mark, and needs to be re-enabled for full GC before
                // we reuse the normal Immix scheduling.
                self.set_ref_closure_buckets_enabled(true);
                crate::plan::immix::global::Immix::schedule_immix_full_heap_collection::<
                    ConcurrentImmix<VM>,
                    ConcurrentImmixSTWGCWorkContext<VM, TRACE_KIND_FAST>,
                    ConcurrentImmixSTWGCWorkContext<VM, TRACE_KIND_DEFRAG>,
                >(self, &self.immix_space, scheduler);
            }
            Pause::InitialMark => self.schedule_concurrent_marking_initial_pause(scheduler),
            Pause::FinalMark => self.schedule_concurrent_marking_final_pause(scheduler),
            Pause::Nursery => {
                // Minors process weak refs/finalizers (dead nursery weakrefs
                // must clear); InitialMark disables these buckets for the
                // concurrent cycle, so re-enable like Full does.
                self.set_ref_closure_buckets_enabled(true);
                scheduler.schedule_common_work::<
                    crate::plan::concurrent::immix::gc_work::ConcurrentImmixNurseryGCWorkContext<VM>,
                >(self);
            }
        }
    }

    fn get_allocator_mapping(&self) -> &'static EnumMap<AllocationSemantics, AllocatorSelector> {
        &ALLOCATOR_MAPPING
    }

    fn prepare(&mut self, tls: VMWorkerThread) {
        let pause = self.current_pause().unwrap();
        match pause {
            Pause::Full => {
                self.common.prepare(tls, true);
                self.immix_space.prepare(
                    true,
                    Some(StatsForDefrag::new(self)),
                    // Unlog bits are persistent under the always-on barrier;
                    // the trace re-arms live objects (test-before-store).
                    // NOTE: do NOT use BulkClear here -- this fork's prepare
                    // defers non-NoOp unlog ops to POST-pause packets, which
                    // would wipe the arming after the trace (disarming every
                    // old object) instead of warming the metadata before it.
                    UnlogBitsOperation::NoOp,
                );
            }
            Pause::InitialMark => {
                // MARKING-GATED BARRIER: no arming happens in this pause at
                // all.  The write-barrier fastpath is gated on
                // MMTK_SATB_MARKING_ACTIVE, so unlog bits are inert outside
                // marking and stay armed from the previous cycle's deferred
                // re-arm pass (fresh chunks are armed at first allocation,
                // common-space objects at allocation).  Enabling the barrier
                // is the flag store in the binding's resume path.
                self.immix_space.prepare_concurrent_initial();

                // The immortal/VM-space bulk mark-bit resets were already
                // performed by the deferred post-pause packet after the last
                // FinalMark/Full (ResetCommonPlanMarkBits); this pause only
                // does the O(1) per-space state flips.
                // A/B kill-switch: MMTK_EAGER_COMMON_RESET restores the
                // upstream in-pause reset (the deferred packet still runs;
                // double-zeroing is harmless).
                if std::env::var_os("MMTK_EAGER_COMMON_RESET").is_some() {
                    self.common.prepare(tls, true);
                } else {
                    self.common.prepare_deferred_mark_reset(tls, true);
                }
            }
            Pause::FinalMark => (),
            Pause::Nursery => {
                // Minor prepare: no mark-state or line-epoch changes (marks
                // persist as the old set; survivor lines are marked with the
                // current epoch at scan time).  Only the LOS needs its
                // logical-nursery flip.
                self.immix_space.prepare(false, None, UnlogBitsOperation::NoOp);
                self.common.los.prepare(false);
            }
        }
    }

    fn release(&mut self, tls: VMWorkerThread) {
        let pause = self.current_pause().unwrap();
        match pause {
            Pause::InitialMark => (),
            Pause::Nursery => {
                // In-pause nursery sweep: reclaims dead nursery lines and
                // feeds them straight back to the allocator (the warm-reuse
                // locality mechanism).  LOS sweeps its logical nursery.
                self.immix_space.sweep_nursery_blocks();
                // If the finalizer sweep was deferred (gate up), the packet
                // performs the LOS release; otherwise do it here as before.
                if !self
                    .immix_space
                    .finalizer_reclaim_gate
                    .load(std::sync::atomic::Ordering::SeqCst)
                {
                    self.common.los.release(false);
                }
            }
            Pause::Full | Pause::FinalMark => {
                // Aborted FinalMark: marking is still in progress, so no
                // release/sweep decisions are valid yet.
                if pause == Pause::FinalMark && self.final_mark_aborted.load(Ordering::SeqCst) {
                    return;
                }
                self.immix_space.release(
                    true,
                    // ALWAYS-ON BARRIER: no bulk re-arm.  A deferred
                    // chunk-wide BulkSet would race the allocator's claim-time
                    // disarm (a range claimed and disarmed after the pause
                    // could be re-armed by the packet, making young objects
                    // look old).  Arming is precise instead: trace-time
                    // arming, the in-pause float promotion in
                    // `ImmixSpace::release`, and the remset drain re-arm.
                    UnlogBitsOperation::NoOp,
                    // ALL collections use the lazy release path: an eager
                    // sweep would walk blocks that are simultaneously members
                    // of the lazy lists/pool, creating duplicate ownership --
                    // the root cause of the MT double-allocation corruption.
                    pause == Pause::FinalMark || pause == Pause::Full,
                );

                // If the finalizer sweep was deferred (gate up), dead LOS
                // objects must stay intact until classified/resurrected --
                // the packet performs the LOS release.
                if self
                    .immix_space
                    .finalizer_reclaim_gate
                    .load(std::sync::atomic::Ordering::SeqCst)
                {
                    self.common.release_defer_los(tls, true);
                } else {
                    self.common.release(tls, true);
                }

                // Re-arm the common spaces (sysimage immortal, LOS) the same
                // way, after every major collection.
                let common_plan =
                    unsafe { &*(&self.common as *const crate::plan::global::CommonPlan<VM>) };
                self.immix_space.defer_post_pause_packet(Box::new(
                    crate::plan::gc_work::SetCommonPlanUnlogBits { common_plan },
                ));
                // Also reset the immortal/VM-space mark bits off-pause, so
                // the next InitialMark's prepare has no metadata sweep left
                // (the bits are unread between cycles; allocations only set
                // them while allocate-as-live is active, i.e. during the
                // marking that just ended).
                self.immix_space.defer_post_pause_packet(Box::new(
                    crate::plan::gc_work::ResetCommonPlanMarkBits { common_plan },
                ));
            }
        }
    }

    fn end_of_gc(&mut self, _tls: VMWorkerThread) {
        self.last_gc_was_defrag
            .store(self.immix_space.end_of_gc(), Ordering::Relaxed);

        let pause = self.current_pause().unwrap();
        {
            let now = crate::diag::now_ns();
            match pause {
                Pause::InitialMark => { self.mark_start_ns.store(now, Ordering::Relaxed); }
                Pause::FinalMark if self.final_mark_aborted.load(Ordering::SeqCst) => {}
                Pause::FinalMark => {
                    let s = self.mark_start_ns.load(Ordering::Relaxed);
                    if s != 0 && now > s {
                        let d = now - s;
                        let prev = self.mark_dur_ns.load(Ordering::Relaxed);
                        let ewma = if prev == 0 { d } else { (prev * 3 + d) / 4 };
                        self.mark_dur_ns.store(ewma, Ordering::Relaxed);
                    }
                }
                Pause::Full | Pause::Nursery => {}
            }
            self.gc_end_ns.store(now, Ordering::Relaxed);
        }
        // DIAG (MMTK_HEAP_TRACE): per-cycle reclaim accounting.
        {
            use std::sync::OnceLock;
            static ON: OnceLock<bool> = OnceLock::new();
            if *ON.get_or_init(|| std::env::var_os("MMTK_HEAP_TRACE").is_some()) {
                eprintln!(
                    "[heap] pause={:?} total_pg={} resv_pg={} live_prev_pg={} clean_blk={} reused_blk={} reusable_pool={} unswept={} pending={}",
                    pause,
                    self.get_total_pages(),
                    self.get_reserved_pages(),
                    self.immix_space.live_prev_pages(),
                    crate::diag::CLEAN_BLOCKS.load(Ordering::SeqCst),
                    crate::diag::REUSED_BLOCKS.load(Ordering::SeqCst),
                    self.immix_space.reusable_blocks.len(),
                    self.immix_space.unswept_len(),
                    self.immix_space.pending_len(),
                );
                eprintln!(
                    "[pacer-req] minor={} overgoal={} promo={} headroom={} float={} | live_prev_pg={} live_now_pg={} float_pg={} headroom_pg={:?} total_pg={}",
                    crate::diag::PACER_REQ_MINOR.load(Ordering::Relaxed),
                    crate::diag::PACER_REQ_OVERGOAL.load(Ordering::Relaxed),
                    crate::diag::PACER_REQ_PROMO.load(Ordering::Relaxed),
                    crate::diag::PACER_REQ_HEADROOM.load(Ordering::Relaxed),
                    crate::diag::PACER_REQ_FLOAT.load(Ordering::Relaxed),
                    self.immix_space.live_prev_pages(),
                    self.immix_space.live_now_pages(),
                    self.immix_space.float_pages(),
                    self.base().gc_trigger.policy.concurrent_headroom_pages(),
                    self.get_total_pages(),
                );
            }
        }
        if pause == Pause::InitialMark {
            self.set_concurrent_marking_state(true);
        }
        // LEG 1: schedule the deferred metadata packets (unlog/mark-bit
        // clears from FinalMark) into the always-open bucket.  Workers pick
        // them up as they wake after the pause; the all-parked rendezvous
        // guarantees completion before the next pause can be scheduled.
        // MUST be no-notify: `end_of_gc` runs from `on_last_parked`, which
        // holds the worker-monitor mutex -- notifying would self-deadlock.
        // `on_last_parked` issues the wake after `on_gc_finished` returns.
        let deferred = self.immix_space.take_deferred_packets();
        if !deferred.is_empty() {
            let bucket = &self.base().scheduler.work_buckets
                [crate::scheduler::WorkBucketStage::Unconstrained];
            for p in deferred {
                bucket.add_boxed_no_notify(p);
            }
        }
        self.malloc_pages_at_last_gc.store(
            crate::util::conversions::bytes_to_pages_up(
                <VM as VMBinding>::VMCollection::vm_live_bytes(),
            ),
            Ordering::Relaxed,
        );
        self.los_pages_at_last_gc.store(
            self.common.get_los().reserved_pages(),
            Ordering::Relaxed,
        );
        self.previous_pause.store(Some(pause), Ordering::SeqCst);
        self.current_pause.store(None, Ordering::SeqCst);
        // FIX C: clear unconditionally.  The flag used to be kept across a `FinalMark` so that a
        // full GC requested mid-cycle would be honoured by the *next* collection -- which meant a
        // single moment of heap pressure cost two degraded collections.  With C.1 we never request
        // a full GC while marking is in progress, so there is nothing to defer.
        self.should_do_full_gc.store(false, Ordering::SeqCst);
        info!("{:?} end", pause);
    }

    fn current_gc_may_move_object(&self) -> bool {
        self.immix_space.in_defrag()
    }

    fn get_collection_reserved_pages(&self) -> usize {
        self.immix_space.defrag_headroom_pages()
    }

    fn get_used_pages(&self) -> usize {
        self.immix_space.reserved_pages() + self.common.get_used_pages()
    }

    fn base(&self) -> &BasePlan<VM> {
        &self.common.base
    }

    fn base_mut(&mut self) -> &mut BasePlan<Self::VM> {
        &mut self.common.base
    }

    fn common(&self) -> &CommonPlan<VM> {
        &self.common
    }

    fn notify_mutators_paused(&self, _scheduler: &GCWorkScheduler<VM>) {
        use crate::vm::ActivePlan;
        let pause = self.current_pause().unwrap();
        match pause {
            Pause::Full => {
                self.set_concurrent_marking_state(false);
                // ALWAYS-ON BARRIER: collect the mutators' remset buffers and
                // trace the entries as conservative extra roots of this STW
                // collection.
                for mutator in <VM as VMBinding>::VMActivePlan::mutators() {
                    mutator.barrier.flush();
                }
                self.drain_remset_rearm();
            }
            Pause::InitialMark => {
                debug_assert!(
                    !self.concurrent_marking_in_progress(),
                    "prev pause: {:?}",
                    self.previous_pause().unwrap()
                );
                // ALWAYS-ON BARRIER: remset entries pending at the snapshot
                // boundary are old objects mutated since the last collection;
                // scanning them (and retaining their current referents) makes
                // them valid SATB work.
                for mutator in <VM as VMBinding>::VMActivePlan::mutators() {
                    mutator.barrier.flush();
                }
                self.drain_remset_rearm();
            }
            Pause::FinalMark => {
                debug_assert!(self.concurrent_marking_in_progress());
                // Flush barrier buffers
                for mutator in <VM as VMBinding>::VMActivePlan::mutators() {
                    mutator.barrier.flush();
                }
                // The remset is drained at every InitialMark/Full and no
                // entries accumulate while marking is active, so this is
                // normally empty; drain defensively (SATB treatment is
                // conservative for any straggler).
                self.drain_remset_rearm();
                // GO-STYLE TERMINATION (detect-and-abort): the flush above
                // routed logged objects to the Concurrent bucket, which is
                // worker-pollable during the pause -- the rendezvous would
                // stretch the pause by the full scan (measured: one growing
                // array = 33-107ms FinalMark pauses).  If the pending SATB
                // work exceeds the budget, abort the termination instead:
                // leave the work in the (closed) Concurrent bucket, keep
                // marking active, and let the ordinary self-trigger retry
                // FinalMark after the concurrent drain.  Convergence: the
                // barrier logs each object at most once per cycle.
                let pending =
                    crate::plan::concurrent::PENDING_SATB_BYTES.load(Ordering::Relaxed);
                let budget = Self::term_budget_bytes();
                if std::env::var_os("MMTK_TERM_TRACE").is_some() {
                    eprintln!(
                        "[term] FinalMark: pending_satb={}B budget={}B",
                        pending, budget
                    );
                }
                if pending > budget {
                    self.final_mark_aborted.store(true, Ordering::SeqCst);
                    let scheduler = &self.base().scheduler;
                    scheduler.work_buckets[WorkBucketStage::Concurrent].close();
                    self.set_ref_closure_buckets_enabled(false);
                } else {
                    self.set_concurrent_marking_state(false);
                }
            }
            Pause::Nursery => {
                debug_assert!(!self.concurrent_marking_in_progress());
                // Collect the mutators' remset buffers and schedule the
                // entries as the minor's extra roots.  ProcessModBuf re-arms
                // each entry and scans it for old->young edges; both happen
                // inside this (fully STW) pause.
                for mutator in <VM as VMBinding>::VMActivePlan::mutators() {
                    mutator.barrier.flush();
                }
                let entries = std::mem::take(&mut *self.remset.lock().unwrap());
                if !entries.is_empty() {
                    use crate::plan::generational::gc_work::{GenNurseryTrace, ProcessModBuf};
                    use crate::policy::gc_work::DEFAULT_TRACE;
                    // Small chunks: remset entries can have large scan
                    // fan-out (module binding tables), and one oversized
                    // packet serializes the pause (measured: a 9.5 ms
                    // ProcessModBuf at teardown).  512 entries per packet
                    // spreads the drain across the workers.
                    for chunk in entries.chunks(512) {
                        self.base().scheduler.work_buckets[WorkBucketStage::Closure].add(
                            ProcessModBuf::<GenNurseryTrace<VM, Self, DEFAULT_TRACE>>::new(
                                chunk.to_vec(),
                            ),
                        );
                    }
                }
            }
        }
        info!("{:?} start", pause);
    }

    fn concurrent(&self) -> Option<&dyn ConcurrentPlan<VM = VM>> {
        Some(self)
    }

    fn generational(
        &self,
    ) -> Option<&dyn crate::plan::generational::global::GenerationalPlan<VM = Self::VM>> {
        Some(self)
    }
}

impl<VM: VMBinding> crate::plan::generational::global::GenerationalPlan for ConcurrentImmix<VM> {
    fn is_current_gc_nursery(&self) -> bool {
        self.current_pause() == Some(Pause::Nursery)
    }

    /// Young = unmarked immix object.  Mark bits persist between collections
    /// as the old-set indicator: survivors of the last trace (or minors'
    /// promotions, or allocate-black floats) are marked; objects allocated
    /// since are born unmarked (claims clear stale marks outside marking).
    fn is_object_in_nursery(&self, object: ObjectReference) -> bool {
        self.immix_space.in_space(object) && !self.immix_space.is_marked(object)
    }

    // Same conservative stance as StickyImmix: for address-only queries
    // (memory-slice barriers) claim "mature", which at worst remembers too
    // much.
    fn is_address_in_nursery(&self, _addr: crate::util::Address) -> bool {
        false
    }

    fn get_mature_physical_pages_available(&self) -> usize {
        self.immix_space.available_physical_pages()
    }

    fn get_mature_reserved_pages(&self) -> usize {
        self.immix_space.reserved_pages()
    }

    fn force_full_heap_collection(&self) {
        self.should_do_full_gc.store(true, Ordering::SeqCst);
    }

    fn last_collection_full_heap(&self) -> bool {
        matches!(
            self.previous_pause(),
            Some(Pause::Full) | Some(Pause::FinalMark)
        )
    }
}

impl<VM: VMBinding> crate::plan::generational::global::GenerationalPlanExt<VM>
    for ConcurrentImmix<VM>
{
    /// The nursery trace: terminates at marked (old) objects.  Strictly
    /// non-moving (the Julia binding pins everything; `TRACE_KIND_FAST`).
    fn trace_object_nursery<Q: crate::ObjectQueue, const KIND: TraceKind>(
        &self,
        queue: &mut Q,
        object: ObjectReference,
        _worker: &mut crate::scheduler::GCWorker<VM>,
    ) -> ObjectReference {
        use crate::plan::generational::global::GenerationalPlan;
        if self.immix_space.in_space(object) {
            if !self.is_object_in_nursery(object) {
                // Mature object: stop here.  Old->young edges are covered by
                // the remembered set.
                return object;
            }
            // Marks the object (promotion: it is now part of the old set),
            // marks its lines, and re-arms its unlog bit
            // (`unlog_traced_object`) so its future mutations are logged.
            return self.immix_space.trace_object_without_moving(queue, object);
        }

        if self.common.los.in_space(object) {
            return self.common.get_los().trace_object::<Q>(queue, object);
        }

        // Immortal/nonmoving/VM-space objects are never nursery members and
        // are not scanned by minors; their outgoing edges are covered by the
        // remembered set (they are armed at allocation).
        object
    }
}

impl<VM: VMBinding> ConcurrentImmix<VM> {
    pub fn new(args: CreateGeneralPlanArgs<VM>) -> Self {
        if *args.options.concurrent_immix_disable_concurrent_marking {
            warn!("Option 'concurrent_immix_disable_concurrent_marking' is set to true. Concurrent marking is disabled for ConcurrentImmix. This will make ConcurrentImmix behave exactly like full heap Immix.");
        }

        let spec = crate::util::metadata::extract_side_metadata(&[
            *VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC,
        ]);

        let mut plan_args = CreateSpecificPlanArgs {
            global_args: args,
            constraints: &CONCURRENT_IMMIX_CONSTRAINTS,
            global_side_metadata_specs: SideMetadataContext::new_global_specs(&spec),
        };

        let immix_args = ImmixSpaceArgs {
            mixed_age: false,
            never_move_objects: false,
        };

        // These buckets are not used in an Immix plan. We can simply disable them.
        // TODO: We should be more systmatic on this, and disable unnecessary buckets for other plans as well.
        let scheduler = &plan_args.global_args.scheduler;
        scheduler.work_buckets[WorkBucketStage::VMRefForwarding].set_enabled(false);
        scheduler.work_buckets[WorkBucketStage::CalculateForwarding].set_enabled(false);
        scheduler.work_buckets[WorkBucketStage::SecondRoots].set_enabled(false);
        scheduler.work_buckets[WorkBucketStage::RefForwarding].set_enabled(false);
        scheduler.work_buckets[WorkBucketStage::FinalizableForwarding].set_enabled(false);
        scheduler.work_buckets[WorkBucketStage::Compact].set_enabled(false);

        // CLAIM-TIME ZEROING FOLLOWS THE NURSERY SCALE (measured at both
        // operating points).  At cache-scale rotations (<= ~16 MB) the zero
        // is the load-bearing warm-up: its dense stream takes the L3-tier
        // reuse misses with deep MLP and the scattered object writes then
        // hit L1/L2; removing it there costs 10-35% wall.  At DRAM-scale
        // rotations the same burst outruns the L2 stream prefetcher and eats
        // unhidden DRAM latency; DIRTY handover wins there (1.25 -> 1.13s at
        // 48 MB), because Julia's own paced allocation writes become the
        // first touch and the prefetcher stays ahead of them -- stock's
        // sweep-at-adoption mechanism, reproduced (fill profiles match
        // stock's: demand-DRAM/L3 parity, L2-fill streaming signature).
        // MMTK_ZERO_MODE={on,off,warm} overrides the automatic choice.
        let zeroed = match std::env::var("MMTK_ZERO_MODE") {
            Ok(v) if v == "off" || v == "0" || v == "pw" => false,
            Ok(_) => true,
            Err(_) => {
                // Boot-time nursery estimate: the trigger's threshold with
                // live=0 (min of the configured nursery and total/6).
                let total_pages = plan_args
                    .global_args
                    .gc_trigger
                    .policy
                    .get_current_heap_size_in_pages();
                let boot_nursery = Self::nursery_threshold_pages().min(total_pages / 6);
                boot_nursery <= 4096 // 16 MB
            }
        };

        ConcurrentImmix {
            immix_space: ImmixSpace::new(
                // MARKING-GATED BARRIER: unlog_traced_object=true so that
                // (a) tracing re-arms every traced object's unlog bit each
                // cycle and (b) defrag `post_copy` arms moved copies.  With
                // the in-pause bulk arming gone, these are the paths that
                // keep every live object armed at each InitialMark
                // (allocation-time chunk arming covers the rest).
                plan_args._get_space_args(
                    "immix",
                    zeroed,
                    false,
                    false,
                    true,
                    VMRequest::discontiguous(),
                ),
                immix_args,
            ),
            common: CommonPlan::new(plan_args),
            last_gc_was_defrag: AtomicBool::new(false),
            current_pause: Atomic::new(None),
            previous_pause: Atomic::new(None),
            should_do_full_gc: AtomicBool::new(false),
            concurrent_marking_active: AtomicBool::new(false),
            mark_start_ns: AtomicU64::new(0),
            mark_dur_ns: AtomicU64::new(0),
            gc_end_ns: AtomicU64::new(0),
            remset: std::sync::Mutex::new(Vec::new()),
            minor_due: AtomicBool::new(false),
            final_mark_aborted: AtomicBool::new(false),
            ragged_epoch: std::sync::atomic::AtomicUsize::new(0),
            ragged_acks: std::sync::atomic::AtomicUsize::new(0),
            ragged_start_ns: AtomicU64::new(0),
            major_due: AtomicBool::new(false),
            malloc_pages_at_last_gc: std::sync::atomic::AtomicUsize::new(0),
            los_pages_at_last_gc: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// ALWAYS-ON BARRIER: drain the remembered set at a major pause by
    /// re-arming every entry, inside the pause.  No scanning is needed: a
    /// major collection traces the current heap from roots, so any live
    /// entry is reached (and trace-armed) anyway.  The re-arm cannot be
    /// deferred or skipped: a live old object whose bit stayed consumed
    /// could be mutated during the upcoming marking and the overwritten
    /// value would escape the SATB snapshot.  (Minor pauses instead drain
    /// entries through `ProcessModBuf`, which scans them for old->young
    /// edges.)
    fn drain_remset_rearm(&self) {
        let entries = std::mem::take(&mut *self.remset.lock().unwrap());
        for obj in entries {
            VM::VMObjectModel::GLOBAL_LOG_BIT_SPEC.store_atomic::<VM, u8>(
                obj,
                1,
                None,
                Ordering::SeqCst,
            );
        }
    }

    /// GENERATIONAL: nursery threshold that triggers a minor collection, in
    /// pages.  Default 64 MB with dirty handover: once the line-state
    /// census made pause cost independent of nursery size, the size sweep
    /// optimum moved from 32 MB up to 64 MB (~65 minors/pass at ~0.3ms,
    /// stall 22-28ms/pass ~ stock's inline young-GC budget; paired reps
    /// beat stock's wall by ~3.4% mean).  Small heaps bind on the total/6
    /// cap and land at cache-scale nurseries with warm-up zeroing instead
    /// (see the zeroed selection in the constructor).  Overridable via
    /// MMTK_NURSERY_MB; MMTK_NURSERY_MB=0 disables minors (majors-only).
    fn nursery_threshold_pages() -> usize {
        static PAGES: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *PAGES.get_or_init(|| {
            let mb = std::env::var("MMTK_NURSERY_MB")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(64);
            mb << (20 - 12)
        })
    }

    /// GO-STYLE TERMINATION: FinalMark in-pause SATB budget (bytes).
    fn term_budget_bytes() -> usize {
        static B: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *B.get_or_init(|| {
            std::env::var("MMTK_TERM_BUDGET_KB")
                .ok()
                .and_then(|v| v.parse::<usize>().ok())
                .unwrap_or(1024)
                << 10
        })
    }

    fn set_ref_closure_buckets_enabled(&self, do_closure: bool) {
        let scheduler = &self.common.base.scheduler;
        scheduler.work_buckets[WorkBucketStage::VMRefClosure].set_enabled(do_closure);
        scheduler.work_buckets[WorkBucketStage::WeakRefClosure].set_enabled(do_closure);
        scheduler.work_buckets[WorkBucketStage::FinalRefClosure].set_enabled(do_closure);
        scheduler.work_buckets[WorkBucketStage::SoftRefClosure].set_enabled(do_closure);
        scheduler.work_buckets[WorkBucketStage::PhantomRefClosure].set_enabled(do_closure);
    }

    pub(crate) fn schedule_concurrent_marking_initial_pause(
        &'static self,
        scheduler: &GCWorkScheduler<VM>,
    ) {
        use crate::scheduler::gc_work::Prepare;

        self.set_ref_closure_buckets_enabled(false);

        scheduler.work_buckets[WorkBucketStage::Unconstrained]
            .add(StopMutators::<ConcurrentImmixGCWorkContext<VM>>::new());
        scheduler.work_buckets[WorkBucketStage::Prepare]
            .add(Prepare::<ConcurrentImmixGCWorkContext<VM>>::new(self));
    }

    fn schedule_concurrent_marking_final_pause(&'static self, scheduler: &GCWorkScheduler<VM>) {
        self.set_ref_closure_buckets_enabled(true);

        // Skip root scanning in the final mark
        scheduler.work_buckets[WorkBucketStage::Unconstrained]
            .add(StopMutators::<ConcurrentImmixGCWorkContext<VM>>::new_no_scan_roots());

        scheduler.work_buckets[WorkBucketStage::Release]
            .add(Release::<ConcurrentImmixGCWorkContext<VM>>::new(self));

        // Sanity
        #[cfg(feature = "sanity")]
        {
            use crate::util::sanity::sanity_checker::ScheduleSanityGC;
            scheduler.work_buckets[WorkBucketStage::Final].add(ScheduleSanityGC::<Self>::new(self));
        }

        // Deal with weak ref and finalizers
        // TODO: Check against schedule_common_work and see if we are still missing any work packet
        type RefTracePolicy<VM> =
            crate::plan::tracing::PlanTrace<ConcurrentImmix<VM>, TRACE_KIND_FAST>;
        // Reference processing.
        // LEG 1 (fewer in-pause stages): Julia only registers WEAK reference
        // candidates (`mmtk_add_weak_candidate` in `jl_gc_new_weakref_th`),
        // so the soft/phantom processors always iterate empty lists, and
        // MMTk's `Finalization` is never fed (Julia finalizers go through
        // the VM-specific `VMProcessWeakRefs` path).  Dropping those packets
        // removes three stage barriers from the FinalMark pause.
        // `RefEnqueue` is kept: it maintains reference-processor state
        // (clears `enqueued_references`, re-allows candidates) and shares
        // the Release stage, so it costs no extra barrier.
        if !*self.base().options.no_reference_types {
            use crate::util::reference_processor::{RefEnqueue, WeakRefProcessing};
            scheduler.work_buckets[WorkBucketStage::WeakRefClosure]
                .add(WeakRefProcessing::<VM>::new());
            scheduler.work_buckets[WorkBucketStage::Release].add(RefEnqueue::<VM>::new());
        }

        // VM-specific weak ref processing
        // Note that ConcurrentImmix does not have a separate forwarding stage,
        // so we don't schedule the `VMForwardWeakRefs` work packet.
        scheduler.work_buckets[WorkBucketStage::VMRefClosure]
            .set_sentinel(Box::new(VMProcessWeakRefs::<RefTracePolicy<VM>>::new()));
    }

    pub fn concurrent_marking_in_progress(&self) -> bool {
        self.concurrent_marking_active.load(Ordering::Acquire)
    }

    fn set_concurrent_marking_state(&self, active: bool) {
        use crate::plan::global::HasSpaces;

        // Tell the spaces to allocate new objects as live
        let allocate_object_as_live = active;
        self.for_each_space(&mut |space: &dyn Space<VM>| {
            space.set_allocate_as_live(allocate_object_as_live);
        });

        // Store the state.
        self.concurrent_marking_active
            .store(active, Ordering::SeqCst);

        // We also set SATB barrier as active -- this is done in Mutator prepare/release.
    }

    pub(super) fn is_concurrent_marking_active(&self) -> bool {
        self.concurrent_marking_active.load(Ordering::SeqCst)
    }

    fn previous_pause(&self) -> Option<Pause> {
        self.previous_pause.load(Ordering::SeqCst)
    }

    fn concurrent_marking_is_disabled(&self) -> bool {
        *self
            .base()
            .options
            .concurrent_immix_disable_concurrent_marking
    }
}

impl<VM: VMBinding> ConcurrentPlan for ConcurrentImmix<VM> {
    fn current_pause(&self) -> Option<Pause> {
        self.current_pause.load(Ordering::SeqCst)
    }

    fn finalizer_defer_packet(&self, w: Box<dyn crate::scheduler::GCWork<VM>>) {
        self.immix_space
            .finalizer_reclaim_gate
            .store(true, Ordering::SeqCst);
        self.immix_space.defer_post_pause_packet(w);
    }

    fn finalizer_resurrect_object(&self, object: crate::util::ObjectReference) -> bool {
        if self.immix_space.in_space(object) {
            return self.immix_space.resurrect_object(object);
        }
        if self.common.los.in_space(object) {
            if crate::memory_manager::is_live_object(object) {
                return false;
            }
            // Marks the object and moves it out of the treadmill set the
            // deferred LOS release will sweep.
            struct DiscardQueue;
            impl crate::ObjectQueue for DiscardQueue {
                fn enqueue(&mut self, _object: crate::util::ObjectReference) {}
            }
            self.common.los.trace_object(&mut DiscardQueue, object);
            return true;
        }
        // Immortal/VM spaces are never reclaimed; stop the walk here.
        false
    }

    fn finalizer_sweep_done(&self) {
        self.immix_space
            .finalizer_reclaim_gate
            .store(false, Ordering::SeqCst);
    }

    fn current_collection_is_user_triggered(&self) -> bool {
        self.base().global_state.is_user_triggered_collection()
    }

    fn finalizer_sweep_pending(&self) -> bool {
        self.immix_space
            .finalizer_reclaim_gate
            .load(Ordering::SeqCst)
    }

    fn final_mark_aborted(&self) -> bool {
        self.final_mark_aborted.load(Ordering::SeqCst)
    }

    fn ragged_flush_ready(&self) -> bool {
        use crate::vm::ActivePlan;
        const RAGGED_TIMEOUT_NS: u64 = 2_000_000;
        let now = crate::diag::now_ns();
        let ep = self.ragged_epoch.load(Ordering::SeqCst);
        if ep == 0 {
            // Open a round: mutators flush+ack from their poll sites; the
            // last ack raises the GC request (see ragged_flush_poll).
            self.ragged_acks.store(0, Ordering::SeqCst);
            self.ragged_start_ns.store(now, Ordering::SeqCst);
            self.ragged_epoch.store(1, Ordering::SeqCst);
            return false;
        }
        let done = self.ragged_acks.load(Ordering::SeqCst)
            >= <VM as VMBinding>::VMActivePlan::number_of_mutators()
            || now.saturating_sub(self.ragged_start_ns.load(Ordering::SeqCst))
                > RAGGED_TIMEOUT_NS;
        if done {
            // Reset for the next cycle's round.
            self.ragged_epoch.store(0, Ordering::SeqCst);
        }
        done
    }

    fn ragged_round_id(&self) -> u64 {
        if self.ragged_epoch.load(Ordering::SeqCst) == 0 {
            return 0;
        }
        self.ragged_start_ns.load(Ordering::SeqCst)
    }

    fn ragged_flush_poll(&self, mutator: &mut crate::Mutator<VM>) {
        if self.ragged_epoch.load(Ordering::SeqCst) == 0
            || !self.concurrent_marking_in_progress()
        {
            return;
        }
        mutator.barrier.flush();
        let acks = self.ragged_acks.fetch_add(1, Ordering::SeqCst) + 1;
        use crate::vm::ActivePlan;
        if acks >= <VM as VMBinding>::VMActivePlan::number_of_mutators() {
            // Do NOT request the pause here: a direct request schedules
            // StopMutators immediately, racing the concurrent drain of the
            // work this very round just flushed (measured: a flushed
            // wrapper's 400ms cascade landing in-pause).  Quiet acks are
            // not "drained" -- only the all-parked self-trigger, which by
            // construction fires when every bucket is empty, may request
            // the FinalMark.  Just make sure the workers are awake to
            // drain and re-evaluate.
            self.base()
                .scheduler
                .worker_monitor
                .notify_work_available(true);
        }
    }

    fn satb_capture_values(&self, values: Vec<crate::util::ObjectReference>) {
        use crate::plan::concurrent::concurrent_marking_work::ProcessModBufSATB;
        if values.is_empty() {
            return;
        }
        debug_assert!(self.concurrent_marking_in_progress());
        self.base().scheduler.work_buckets[WorkBucketStage::Concurrent]
            .add(ProcessModBufSATB::<VM, Self, TRACE_KIND_FAST>::new(values));
    }

    fn concurrent_work_in_progress(&self) -> bool {
        self.concurrent_marking_in_progress()
    }

    fn live_pages_estimate(&self) -> Option<usize> {
        // Immix live from the previous major PLUS minor promotion since
        // (live_bytes accumulates each first-time mark and minors' marks are
        // promotions), plus the (stably accounted) common spaces.  The max
        // covers the mid-marking window where live_bytes is still being
        // rebuilt.
        let immix = self
            .immix_space
            .live_prev_pages()
            .max(self.immix_space.live_now_pages());
        Some(immix + self.common.get_used_pages())
    }

    fn append_remset(&self, buf: Vec<ObjectReference>) {
        self.remset.lock().unwrap().extend(buf);
    }

    fn enqueue_satb_values(&self, values: Vec<crate::util::ObjectReference>) {
        use crate::plan::concurrent::concurrent_marking_work::ProcessModBufSATB;
        if values.is_empty() {
            return;
        }
        // Same stage the barrier's own FinalMark flush uses; these values are
        // traced before the weak-ref/finalizer stages read mark bits.
        self.base().scheduler.work_buckets[WorkBucketStage::Closure]
            .add(ProcessModBufSATB::<VM, Self, TRACE_KIND_FAST>::new(values));
    }
}
