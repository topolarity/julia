use log::{info, trace};
use mmtk::plan::Plan;
use mmtk::util::constants::BYTES_IN_PAGE;
use mmtk::util::conversions;
use mmtk::util::heap::{GCTriggerPolicy, SpaceStats};
use mmtk::util::os::{OSMemory, OS};
use mmtk::MMTK;

use crate::{jl_gc_get_hard_heap_limit, jl_gc_get_max_memory, jl_hrtime, JuliaVM};

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

const DEFAULT_COLLECT_INTERVAL: usize = 5600 * 1024 * std::mem::size_of::<usize>();
const GC_ALWAYS_SWEEP_FULL: bool = false;
const ALLOC_SMOOTH_FACTOR: f64 = 0.95;
const COLLECT_SMOOTH_FACTOR: f64 = 0.5;
const TUNING_FACTOR: f64 = 2e4;

// PACING (Go-pacer-style): a concurrent cycle reclaims nothing until it
// completes, so the heap target must leave enough headroom for the mutators
// to allocate through an entire cycle, and the next cycle must be REQUESTED
// at least one cycle's worth of allocation before the target is reached.
// Under fully-lazy sweeping the memory freed by cycle N only becomes
// reusable while cycle N+1 runs (aged-backlog lag), so the wall must cover
// roughly TWO cycles of allocation; the third unit is margin for
// cycle-duration variance and allocation bursts.
const PACING_MARGIN: f64 = 3.0;
/// Headroom must also be at least this fraction of the live set (footprint
/// bound, GOGC-flavored) so tiny cycle-duration estimates cannot collapse it.
const MIN_HEADROOM_LIVE_FRAC: f64 = 0.2;
/// Extra multiplicative growth applied when a mutator was observed blocking
/// in `block_for_gc` during the previous cycle window: direct feedback on
/// the exact failure the pacing exists to prevent (the balancer's own
/// pause/mutator-time inputs cannot see it).
const BLOCKED_GROWTH_FACTOR: f64 = 1.5;

/// Julia-style heap sizing heuristics for MMTk.
///
/// `max_total_memory` is a soft limit derived from Julia's heap size hint logic.
/// `hard_heap_limit` is a hard post-GC limit that overrides the dynamic target.
pub struct JuliaGCTrigger {
    heap_target: AtomicUsize,
    max_heap_size: AtomicUsize,
    max_total_memory: AtomicUsize,
    hard_heap_limit: AtomicUsize,
    old_pause_time: AtomicUsize,
    old_mut_time: AtomicUsize,
    old_heap_size: AtomicUsize,
    old_alloc_diff: AtomicUsize,
    old_freed_diff: AtomicUsize,
    gc_start_time: AtomicUsize,
    gc_end_time: AtomicUsize,
    mutator_time: AtomicUsize,
    thrash_counter: AtomicUsize,
    thrashing: AtomicBool,
    before_free_heap_size: AtomicUsize,
    next_sweep_full: AtomicBool,
    pending_pages: AtomicUsize,
    heap_size_after_last_full_gc: AtomicUsize,
    /// Timestamp (jl_hrtime) of the InitialMark pause that opened the
    /// current concurrent cycle; 0 when no cycle is in flight.
    cycle_start_time: AtomicUsize,
    /// EWMA of the full concurrent-cycle duration in ns (InitialMark start
    /// to FinalMark end -- the reclamation latency, NOT the pause time).
    cycle_dur_ns: AtomicUsize,
    /// EWMA of the mutator allocation rate in bytes/sec, measured over
    /// UNBLOCKED mutator wall time between cycle ends.
    alloc_rate_bps: AtomicUsize,
    /// `BLOCK_TOTAL_NS` snapshot at the last cycle end, to attribute
    /// blocking to the most recent cycle window.
    blocked_ns_snapshot: AtomicUsize,
    /// `jl_hrtime` of the last cycle end (FinalMark or Full).
    cycle_end_time: AtomicUsize,
    /// Reserved bytes at the last cycle end (post-release).
    heap_at_cycle_end: AtomicUsize,
    /// Published pacing headroom in bytes (`alloc_rate * cycle_dur * margin`):
    /// how much allocation a full cycle must be able to ride out.  Read by
    /// the plan's advisory trigger via `concurrent_headroom_pages`.
    pacing_headroom_bytes: AtomicUsize,
}

/// The current pause kind, matched on `Debug` (the `Pause` enum lives in a
/// private mmtk-core module).  `None` for non-concurrent plans, where every
/// collection is its own complete cycle.
fn current_pause_kind(mmtk: &'static MMTK<JuliaVM>) -> Option<&'static str> {
    let cp = mmtk.get_plan().concurrent()?;
    let p = cp.current_pause()?;
    match format!("{:?}", p).as_str() {
        "InitialMark" => Some("initial"),
        "FinalMark" => Some("final"),
        "Full" => Some("full"),
        "Nursery" => Some("nursery"),
        _ => None,
    }
}

impl JuliaGCTrigger {
    pub fn new() -> Self {
        let max_memory = unsafe { jl_gc_get_max_memory() };
        let total_memory = OS::get_system_total_memory().unwrap() as usize;
        let max_total_mem = std::cmp::min(max_memory, total_memory);
        let hard_heap_limit = unsafe { jl_gc_get_hard_heap_limit() };
        let initial_target = if hard_heap_limit != 0 {
            hard_heap_limit
        } else {
            DEFAULT_COLLECT_INTERVAL
        };

        Self {
            heap_target: AtomicUsize::new(initial_target),
            max_heap_size: AtomicUsize::new(total_memory),
            max_total_memory: AtomicUsize::new(max_total_mem),
            hard_heap_limit: AtomicUsize::new(hard_heap_limit),
            old_pause_time: AtomicUsize::new(1e7 as usize),
            old_mut_time: AtomicUsize::new(1e9 as usize),
            old_heap_size: AtomicUsize::new(0),
            old_alloc_diff: AtomicUsize::new(DEFAULT_COLLECT_INTERVAL),
            old_freed_diff: AtomicUsize::new(DEFAULT_COLLECT_INTERVAL),
            gc_start_time: AtomicUsize::new(0),
            gc_end_time: AtomicUsize::new(0),
            mutator_time: AtomicUsize::new(0),
            thrash_counter: AtomicUsize::new(0),
            thrashing: AtomicBool::new(false),
            before_free_heap_size: AtomicUsize::new(0),
            next_sweep_full: AtomicBool::new(false),
            pending_pages: AtomicUsize::new(0),
            heap_size_after_last_full_gc: AtomicUsize::new(0),
            cycle_start_time: AtomicUsize::new(0),
            cycle_dur_ns: AtomicUsize::new(0),
            alloc_rate_bps: AtomicUsize::new(0),
            blocked_ns_snapshot: AtomicUsize::new(0),
            cycle_end_time: AtomicUsize::new(0),
            heap_at_cycle_end: AtomicUsize::new(0),
            pacing_headroom_bytes: AtomicUsize::new(0),
        }
    }

    fn user_max(&self) -> usize {
        self.max_total_memory.load(Ordering::Relaxed) * 80 / 100
    }

    fn maybe_force_full_heap(&self, mmtk: &'static MMTK<JuliaVM>) {
        if let Some(gen) = mmtk.get_plan().generational() {
            if self.next_sweep_full.load(Ordering::Relaxed) || GC_ALWAYS_SWEEP_FULL {
                gen.force_full_heap_collection();
            }
        }
    }
}

impl GCTriggerPolicy<JuliaVM> for JuliaGCTrigger {
    fn on_gc_start(&self, mmtk: &'static MMTK<JuliaVM>) {
        self.maybe_force_full_heap(mmtk);

        let reserved_pages_now =
            mmtk.get_plan().get_reserved_pages() + self.pending_pages.load(Ordering::SeqCst);
        let now = unsafe { jl_hrtime() } as usize;

        self.gc_start_time.store(now, Ordering::Relaxed);
        self.mutator_time.store(
            if self.gc_end_time.load(Ordering::Relaxed) == 0 {
                self.old_mut_time.load(Ordering::Relaxed)
            } else {
                now - self.gc_end_time.load(Ordering::Relaxed)
            },
            Ordering::Relaxed,
        );
        self.before_free_heap_size.store(
            conversions::pages_to_bytes(reserved_pages_now),
            Ordering::Relaxed,
        );

        trace!(
            "GC start: reserved_pages_now={}, mutator_time={}, before_free_heap_size={}, next_sweep_full={}",
            reserved_pages_now,
            self.mutator_time.load(Ordering::Relaxed),
            self.before_free_heap_size.load(Ordering::Relaxed),
            self.next_sweep_full.load(Ordering::Relaxed),
        );
    }

    fn on_gc_end(&self, mmtk: &'static MMTK<JuliaVM>) {
        let gc_end_time = unsafe { jl_hrtime() } as usize;
        #[allow(unused_mut)]
        let mut pause = gc_end_time - self.gc_start_time.load(Ordering::Relaxed);
        self.gc_end_time.store(gc_end_time, Ordering::Relaxed);

        // CONCURRENT PACING: the balancer must run once per CYCLE with the
        // cycle's true reclamation latency, not once per pause with the
        // pause duration.  An InitialMark ends with nothing reclaimed and a
        // sub-ms "pause" -- feeding it to the balancer teaches it that
        // collection is nearly free, which collapses the heap target to its
        // floor and turns every cycle into a synchronous block at the wall.
        let kind = current_pause_kind(mmtk);
        let is_concurrent_plan = mmtk.get_plan().concurrent().is_some();
        if kind == Some("initial") {
            // The cycle opened at this pause's start; the balancer runs at
            // the matching FinalMark end with the full span.
            self.cycle_start_time
                .store(self.gc_start_time.load(Ordering::Relaxed), Ordering::Relaxed);
            return;
        }
        if kind == Some("nursery") {
            // A minor pause is not a major-cycle boundary: it must not feed
            // the balancer or shift the cycle accounting (rate/target
            // updates run on InitialMark..FinalMark spans).  Post-minor live
            // feeding is Phase 2 work.
            return;
        }

        let pending_pages = self.pending_pages.swap(0, Ordering::SeqCst);
        let reserved_pages_now = mmtk.get_plan().get_reserved_pages() + pending_pages;
        let heap_size = conversions::pages_to_bytes(reserved_pages_now);
        let user_max = self.user_max();
        let hard_heap_limit = self.hard_heap_limit.load(Ordering::Relaxed);

        // Saturating: reserved can SHRINK across a window (lazy-sweep triage
        // releasing backlog); wrapping here poisons the rate estimate with
        // ~2^64 spikes that the EWMA then takes many cycles to forget.
        let alloc_diff = self
            .before_free_heap_size
            .load(Ordering::Relaxed)
            .saturating_sub(self.old_heap_size.load(Ordering::Relaxed));
        let freed_diff = self
            .before_free_heap_size
            .load(Ordering::Relaxed)
            .wrapping_sub(heap_size);
        self.old_heap_size.store(heap_size, Ordering::Relaxed);

        // Cycle span and unblocked mutator time for this window.  For a
        // FinalMark, the cycle opened at the InitialMark pause; for Full (or
        // a non-concurrent plan) the collection is its own complete cycle.
        let cycle_start = match kind {
            Some("final") => {
                let cs = self.cycle_start_time.swap(0, Ordering::Relaxed);
                if cs != 0 {
                    cs
                } else {
                    self.gc_start_time.load(Ordering::Relaxed)
                }
            }
            _ => self.gc_start_time.load(Ordering::Relaxed),
        };
        let cycle_dur = gc_end_time.saturating_sub(cycle_start).max(1);
        let prev_cycle_end = self.cycle_end_time.swap(gc_end_time, Ordering::Relaxed);
        let blocked_now = crate::BLOCK_TOTAL_NS.load(std::sync::atomic::Ordering::SeqCst) as usize;
        let blocked_delta =
            blocked_now.saturating_sub(self.blocked_ns_snapshot.swap(blocked_now, Ordering::Relaxed));
        self.heap_at_cycle_end.store(heap_size, Ordering::Relaxed);

        if is_concurrent_plan {
            // Balancer inputs, corrected for concurrency:
            //  - gc cost = the full cycle span (reclamation latency);
            //  - mutator time = wall since the previous cycle end, EXCLUDING
            //    time the requester spent blocked in block_for_gc (otherwise
            //    the damage of a cramped target reads as mutator progress).
            let window = gc_end_time.saturating_sub(prev_cycle_end.min(gc_end_time));
            let unblocked = window.saturating_sub(blocked_delta).max(1);
            pause = cycle_dur;
            self.mutator_time.store(unblocked, Ordering::Relaxed);

            // Measured allocation rate (bytes/sec) over unblocked time, and
            // the pacing headroom: the allocation a full cycle must be able
            // to ride out without hitting the target wall.
            // Update the rate EWMA only from meaningful windows: a shrink
            // (alloc_diff saturated to 0) or a degenerate window carries no
            // rate information -- keep the previous estimate.
            let old_rate = self.alloc_rate_bps.load(Ordering::Relaxed);
            let rate = if alloc_diff > 0 && unblocked > 1_000_000 {
                let raw = (alloc_diff as f64) / (unblocked as f64 / 1e9);
                let smoothed = if old_rate == 0 || !raw.is_finite() {
                    raw.max(0.0)
                } else {
                    mmtk_jl_gc_smooth(old_rate, raw as usize, COLLECT_SMOOTH_FACTOR) as f64
                };
                self.alloc_rate_bps.store(smoothed as usize, Ordering::Relaxed);
                smoothed
            } else {
                old_rate as f64
            };
            // Cycle-duration estimate: only CONCURRENT cycles inform it (a
            // Full's STW duration is not the reclamation latency the pacing
            // must ride out), and it tracks conservatively -- jumps up to a
            // slower cycle immediately, decays slowly -- because a pacing
            // sized to the mean cycle blocks on every slower-than-mean one.
            let old_cd = self.cycle_dur_ns.load(Ordering::Relaxed);
            let cd = if kind != Some("final") {
                old_cd
            } else if old_cd == 0 || cycle_dur > old_cd {
                cycle_dur
            } else {
                mmtk_jl_gc_smooth(old_cd, cycle_dur, 0.9)
            };
            self.cycle_dur_ns.store(cd, Ordering::Relaxed);
            let pacing = rate * (cd as f64 / 1e9) * PACING_MARGIN;
            self.pacing_headroom_bytes
                .store(pacing.min(user_max as f64 / 2.0) as usize, Ordering::Relaxed);

            // DIAG (env MMTK_PACER_TRACE): one line per cycle with the raw
            // pacer inputs, for in-system validation of the heuristics.
            {
                use std::sync::OnceLock;
                static TRACE: OnceLock<bool> = OnceLock::new();
                if *TRACE.get_or_init(|| std::env::var_os("MMTK_PACER_TRACE").is_some()) {
                    eprintln!(
                        "[pacer] kind={:?} cycle_dur={:.1}ms window={:.1}ms blocked={:.1}ms alloc_diff={:.1}MB rate={:.2}GB/s cd_ewma={:.1}ms pacing={:.1}MB heap_size={:.1}MB",
                        kind,
                        cycle_dur as f64 / 1e6,
                        window as f64 / 1e6,
                        blocked_delta as f64 / 1e6,
                        alloc_diff as f64 / 1048576.0,
                        rate / 1e9,
                        cd as f64 / 1e6,
                        pacing / 1048576.0,
                        heap_size as f64 / 1048576.0,
                    );
                }
            }
        }

        let gc_auto = !mmtk.is_user_triggered_collection();
        if gc_auto && hard_heap_limit == 0 {
            let mut target_allocs = 0.0;
            let alloc_mem = mmtk_jl_gc_smooth(
                self.old_alloc_diff.load(Ordering::Relaxed),
                alloc_diff,
                ALLOC_SMOOTH_FACTOR,
            );
            let alloc_time = mmtk_jl_gc_smooth(
                self.old_mut_time.load(Ordering::Relaxed),
                self.mutator_time.load(Ordering::Relaxed),
                ALLOC_SMOOTH_FACTOR,
            );
            let gc_mem = mmtk_jl_gc_smooth(
                self.old_freed_diff.load(Ordering::Relaxed),
                freed_diff,
                COLLECT_SMOOTH_FACTOR,
            );
            let gc_time = mmtk_jl_gc_smooth(
                self.old_pause_time.load(Ordering::Relaxed),
                pause,
                COLLECT_SMOOTH_FACTOR,
            );

            self.old_alloc_diff.store(alloc_mem, Ordering::Relaxed);
            self.old_mut_time.store(alloc_time, Ordering::Relaxed);
            self.old_freed_diff.store(gc_mem, Ordering::Relaxed);
            self.old_pause_time.store(gc_time, Ordering::Relaxed);

            let thrash_counter = self.thrash_counter.load(Ordering::Relaxed);
            if pause > self.mutator_time.load(Ordering::Relaxed) && thrash_counter <= 4 {
                self.thrash_counter
                    .store(thrash_counter + 1, Ordering::Relaxed);
            } else if thrash_counter > 0 {
                self.thrash_counter
                    .store(thrash_counter - 1, Ordering::Relaxed);
            }

            if alloc_mem != 0 && alloc_time != 0 && gc_mem != 0 && gc_time != 0 {
                let alloc_rate = alloc_mem as f64 / alloc_time as f64;
                let gc_rate = gc_mem as f64 / gc_time as f64;
                target_allocs = (heap_size as f64 * alloc_rate / gc_rate).sqrt() * TUNING_FACTOR;
            }

            if !self.thrashing.load(Ordering::Relaxed)
                && self.thrash_counter.load(Ordering::Relaxed) >= 3
            {
                self.thrashing.store(true, Ordering::Relaxed);
                self.thrash_counter.store(6, Ordering::Relaxed);
            } else if self.thrashing.load(Ordering::Relaxed)
                && self.thrash_counter.load(Ordering::Relaxed) <= 2
            {
                self.thrashing.store(false, Ordering::Relaxed);
            }

            let mut target_heap = target_allocs + heap_size as f64;
            let mut min_target_allocs = heap_size / 20;
            if min_target_allocs < DEFAULT_COLLECT_INTERVAL / 8 {
                min_target_allocs = DEFAULT_COLLECT_INTERVAL / 8;
            }
            let mut max_target_allocs = mmtk_overallocation(
                self.before_free_heap_size.load(Ordering::Relaxed),
                heap_size,
                user_max,
            );
            if max_target_allocs < min_target_allocs {
                max_target_allocs = min_target_allocs;
            }

            if target_heap > user_max as f64 {
                target_allocs = if heap_size < user_max {
                    (user_max - heap_size) as f64
                } else {
                    1.0
                };
            }

            if self.thrashing.load(Ordering::Relaxed) {
                let thrashing_allocs =
                    ((min_target_allocs as f64) * (max_target_allocs as f64)).sqrt();
                if target_allocs < thrashing_allocs {
                    target_allocs = thrashing_allocs;
                }
            }

            if target_allocs > max_target_allocs as f64 {
                target_allocs = max_target_allocs as f64;
            } else if target_allocs < min_target_allocs as f64 {
                target_allocs = min_target_allocs as f64;
            }

            // CONCURRENT PACING FLOORS: the balancer's headroom is an
            // interval tuned for collectors whose reclamation is immediate
            // when the threshold is hit.  A concurrent cycle reclaims only
            // at its END, so headroom below `alloc_rate x cycle_duration`
            // guarantees the mutator hits the wall mid-cycle and blocks for
            // the remainder -- the measured 79%-blocked steady state.  Floor
            // it at the measured pacing headroom and a fraction of live;
            // observed blocking is direct evidence the target is still
            // cramped, so grow through it.
            // For concurrent plans, base the target on the LIVE estimate,
            // not reserved: lazy sweeping keeps dead-but-untriaged blocks in
            // `reserved`, so a reserved-based target compounds its own float
            // allowance into runaway growth (measured: 10-38GB targets on a
            // ~200MB workload).
            let live_bytes = mmtk
                .get_plan()
                .concurrent()
                .and_then(|cp| cp.live_pages_estimate())
                .map(conversions::pages_to_bytes)
                .filter(|b| *b > 0);
            if is_concurrent_plan {
                let base = live_bytes.unwrap_or(heap_size) as f64;
                let mut floor = self.pacing_headroom_bytes.load(Ordering::Relaxed) as f64;
                let live_floor = base * MIN_HEADROOM_LIVE_FRAC;
                if floor < live_floor {
                    floor = live_floor;
                }
                if target_allocs < floor {
                    target_allocs = floor;
                }
                if blocked_delta > 0 {
                    target_allocs *= BLOCKED_GROWTH_FACTOR;
                }
            }

            let target_base = if is_concurrent_plan {
                live_bytes.unwrap_or(heap_size)
            } else {
                heap_size
            };
            target_heap = target_allocs + target_base as f64;
            if target_heap < DEFAULT_COLLECT_INTERVAL as f64 {
                target_heap = DEFAULT_COLLECT_INTERVAL as f64;
            }
            if target_heap > user_max as f64 {
                target_heap = user_max as f64;
            }
            self.heap_target
                .store(target_heap as usize, Ordering::Relaxed);
        } else if hard_heap_limit != 0 {
            self.heap_target.store(hard_heap_limit, Ordering::Relaxed);
        }

        if hard_heap_limit != 0 && heap_size > hard_heap_limit {
            eprintln!("Heap size exceeded hard limit of {hard_heap_limit} bytes.");
            std::process::abort();
        }

        let last_collection_full_heap = mmtk
            .get_plan()
            .generational()
            .is_some_and(|gen| gen.last_collection_full_heap());
        if !mmtk.get_plan().generational().is_some() || last_collection_full_heap {
            self.heap_size_after_last_full_gc
                .store(heap_size, Ordering::Relaxed);
        }

        let heap_size_after_last_full_gc =
            self.heap_size_after_last_full_gc.load(Ordering::Relaxed);
        let large_heap_growth = if heap_size_after_last_full_gc == 0 {
            false
        } else {
            let expected_heap_size = heap_size_after_last_full_gc
                + mmtk_overallocation(heap_size_after_last_full_gc, 0, usize::MAX);
            heap_size > expected_heap_size
        };
        let next_sweep_full = GC_ALWAYS_SWEEP_FULL || heap_size > user_max || large_heap_growth;
        self.next_sweep_full
            .store(next_sweep_full, Ordering::Relaxed);

        trace!(
            "GC end: heap_size={}, heap_target={}, user_max={}, hard_heap_limit={}, next_sweep_full={}",
            heap_size,
            self.heap_target.load(Ordering::Relaxed),
            user_max,
            hard_heap_limit,
            next_sweep_full,
        );

        if self.thrashing.load(Ordering::Relaxed) {
            info!(
                "GC thrashing detected: heap_size={}, heap_target={}",
                heap_size,
                self.heap_target.load(Ordering::Relaxed)
            );
        }
    }

    fn on_pending_allocation(&self, pages: usize) {
        self.pending_pages.fetch_add(pages, Ordering::SeqCst);
    }

    fn is_gc_required(
        &self,
        space_full: bool,
        space: Option<SpaceStats<JuliaVM>>,
        plan: &dyn Plan<VM = JuliaVM>,
    ) -> bool {
        if self.is_heap_full(plan) {
            // Non-concurrent plans: crossing the target means collect now
            // (blocking), and the collection reclaims immediately -- the
            // original semantics.
            if plan.concurrent().is_none() {
                return true;
            }
            // Concurrent plans: the target is a heuristic GOAL, not a limit
            // (Go-pacer semantics).  Exceeding it must only ever REQUEST a
            // cycle -- the plan's advisory paths do that -- while allocation
            // proceeds as float; parking a mutator for a whole cycle, or
            // forcing a synchronous Full, is never an acceptable trade
            // against floating garbage.  Blocking semantics are reserved
            // for true walls: a user-configured hard limit, or the absolute
            // memory ceiling.
            let hard = self.hard_heap_limit.load(Ordering::Relaxed);
            let ceiling = if hard != 0 { hard } else { self.user_max() };
            let reserved_bytes = conversions::pages_to_bytes(
                plan.get_reserved_pages() + self.pending_pages.load(Ordering::SeqCst),
            );
            if reserved_bytes >= ceiling {
                if mmtk::diag::pacer_trace_enabled() {
                    eprintln!(
                        "[pacer-block] reserved {}MB >= ceiling {}MB (hard={}): escalating",
                        reserved_bytes / 1048576,
                        ceiling / 1048576,
                        self.hard_heap_limit.load(Ordering::Relaxed) != 0
                    );
                }
                return plan.collection_required(true, space);
            }
            return plan.collection_required(space_full, space);
        }

        plan.collection_required(space_full, space)
    }

    fn is_heap_full(&self, plan: &dyn Plan<VM = JuliaVM>) -> bool {
        let reserved_pages_now =
            plan.get_reserved_pages() + self.pending_pages.load(Ordering::SeqCst);
        let heap_size = conversions::pages_to_bytes(reserved_pages_now);
        let heap_target = self.heap_target.load(Ordering::Relaxed);

        trace!("Heap size = {}, heap target = {}", heap_size, heap_target);
        heap_size >= heap_target
    }

    fn concurrent_headroom_pages(&self) -> Option<usize> {
        let bytes = self.pacing_headroom_bytes.load(Ordering::Relaxed);
        if bytes == 0 {
            None
        } else {
            Some(bytes.div_ceil(BYTES_IN_PAGE))
        }
    }

    fn get_current_heap_size_in_pages(&self) -> usize {
        self.heap_target.load(Ordering::Relaxed) / BYTES_IN_PAGE
    }

    fn get_max_heap_size_in_pages(&self) -> usize {
        let hard_heap_limit = self.hard_heap_limit.load(Ordering::Relaxed);
        let heap_limit = if hard_heap_limit != 0 {
            hard_heap_limit
        } else {
            self.max_heap_size.load(Ordering::Relaxed)
        };
        heap_limit / BYTES_IN_PAGE
    }

    fn can_heap_size_grow(&self) -> bool {
        true
    }
}

fn mmtk_jl_gc_smooth(old_val: usize, new_val: usize, factor: f64) -> usize {
    let est = factor * old_val as f64 + (1.0 - factor) * new_val as f64;
    if est <= 1.0 {
        1
    } else if est > (2usize << 36) as f64 {
        2usize << 36
    } else {
        est as usize
    }
}

fn mmtk_overallocation(old_val: usize, val: usize, max_val: usize) -> usize {
    let exp2 = usize::BITS as usize - old_val.leading_zeros() as usize;
    let inc = (1usize << (exp2 * 7 / 8)) * 4 + old_val / 8;
    if inc + val > max_val && inc > max_val / 20 {
        max_val / 20
    } else {
        inc
    }
}
