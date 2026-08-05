// Use the `{likely, unlikely}` provided by compiler when using nightly
#![cfg_attr(feature = "nightly", feature(core_intrinsics))]

//! Memory Management ToolKit (MMTk) is a portable and high performance memory manager
//! that includes various garbage collection algorithms and provides clean and efficient
//! interfaces to cooperate with language implementations. MMTk features highly modular
//! and highly reusable designs. It includes components such as allocators, spaces and
//! work packets that GC implementers can choose from to compose their own GC plan easily.
//!
//! Logically, this crate includes these major parts:
//! * GC components:
//!   * [Allocators](util/alloc/allocator/trait.Allocator.html): handlers of allocation requests which allocate objects to the bound space.
//!   * [Policies](policy/space/trait.Space.html): definitions of semantics and behaviors for memory regions.
//!     Each space is an instance of a policy, and takes up a unique proportion of the heap.
//!   * [Work packets](scheduler/work/trait.GCWork.html): units of GC work scheduled by the MMTk's scheduler.
//! * [GC plans](plan/global/trait.Plan.html): GC algorithms composed from components.
//! * [Heap implementations](util/heap/index.html): the underlying implementations of memory resources that support spaces.
//! * [Scheduler](scheduler/scheduler/struct.GCWorkScheduler.html): the MMTk scheduler to allow flexible and parallel execution of GC work.
//! * Interfaces: bi-directional interfaces between MMTk and language implementations
//!   i.e. [the memory manager API](memory_manager/index.html) that allows a language's memory manager to use MMTk
//!   and [the VMBinding trait](vm/trait.VMBinding.html) that allows MMTk to call the language implementation.

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate log;
#[macro_use]
extern crate downcast_rs;
#[macro_use]
extern crate static_assertions;
#[macro_use]
extern crate probe;

mod mmtk;
pub use mmtk::MMTKBuilder;
pub(crate) use mmtk::MMAPPER;
pub use mmtk::MMTK;

mod global_state;
pub use crate::global_state::LiveBytesStats;

mod policy;

pub mod build_info;
pub mod memory_manager;
pub mod plan;
pub mod scheduler;

/// Diagnostics for GC-request -> pause latency (added for investigation).
pub mod diag {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
    use std::sync::OnceLock;
    use std::time::Instant;
    static ORIGIN: OnceLock<Instant> = OnceLock::new();
    pub fn now_ns() -> u64 { ORIGIN.get_or_init(Instant::now).elapsed().as_nanos() as u64 }
    pub static REQUEST_NS: AtomicU64 = AtomicU64::new(0);
    pub static LAT_TOTAL_NS: AtomicU64 = AtomicU64::new(0);
    pub static LAT_MAX_NS: AtomicU64 = AtomicU64::new(0);
    pub static LAT_COUNT: AtomicU64 = AtomicU64::new(0);
    pub static PKTS_SINCE_REQ: AtomicUsize = AtomicUsize::new(0);
    pub static PKTS_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static PKT_NS_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static PARK_EVENTS: AtomicU64 = AtomicU64::new(0);
    pub static BUSY_AT_REQ_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static REQ_PENDING: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
    pub static PKT_MAX_IN_WIN_NS: AtomicU64 = AtomicU64::new(0);   // longest single packet during a pending window
    pub static PKT_SUM_IN_WIN_NS: AtomicU64 = AtomicU64::new(0);   // summed packet CPU time during pending windows
    pub static PKT_MAX_ANY_NS: AtomicU64 = AtomicU64::new(0);      // longest single packet, ever
    pub static SELF_TRIGGERED: AtomicU64 = AtomicU64::new(0);      // final-mark pauses raised by the collector
    pub static NOREQ_PARKS: AtomicU64 = AtomicU64::new(0);          // reached 'no request' branch
    pub static NOREQ_CONCURRENT_SOME: AtomicU64 = AtomicU64::new(0);// ...and plan.concurrent() was Some
    pub static NOREQ_CM_ACTIVE: AtomicU64 = AtomicU64::new(0);      // ...and marking was in progress
    pub static SWEEP_NS: AtomicU64 = AtomicU64::new(0);             // CPU time in SweepChunk packets
    pub static SWEEP_PKTS: AtomicU64 = AtomicU64::new(0);           // number of SweepChunk packets
    /// FIX E-prio: set while a GC goal is pending, so workers stop dispatching new
    /// `Concurrent` packets and can reach the all-parked rendezvous promptly.
    /// Number of SweepChunk packets queued but not yet finished (concurrent sweep).
    pub static SWEEP_OUTSTANDING: AtomicU64 = AtomicU64::new(0);
    pub static TRIAGE_CHUNKS: AtomicU64 = AtomicU64::new(0);
    pub static TRIAGE_MAX_NS: AtomicU64 = AtomicU64::new(0);   // longest single lazy_triage_some call (mutator stall)
    pub static TRIAGE_NS_TOTAL: AtomicU64 = AtomicU64::new(0);
    pub static UNLOG_MAX_NS: AtomicU64 = AtomicU64::new(0);    // longest serial bulk unlog inside a pause
    /// Set by the binding while the world is stopped; workers report slow
    /// packets executed inside the pause window.
    pub static PAUSE_ACTIVE: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    /// Mirror of the binding's SATB marking-active flag, for policy code
    /// that cannot reach the plan (e.g. VMSpace registration must not arm
    /// unlog bits mid-marking: half-relocated image objects would fire the
    /// snapshot barrier).
    pub static SATB_MARKING_ACTIVE: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    /// Threshold (ns) above which an in-pause packet is reported to stderr.
    pub static PAUSE_PKT_REPORT_NS: AtomicU64 = AtomicU64::new(u64::MAX);
    /// Per-pause packet accounting (reset by the binding at pause start):
    /// distinguishes work-bound pauses (sum ~ duration x workers) from
    /// barrier/straggler-bound pauses (sum << duration x workers).
    pub static PAUSE_PKT_SUM_NS: AtomicU64 = AtomicU64::new(0);
    pub static PAUSE_PKT_N: AtomicU64 = AtomicU64::new(0);
    pub static PAUSE_PKT_MAX_NS: AtomicU64 = AtomicU64::new(0);
    /// Timestamp of `on_gc_finished` entry (all buckets drained); the
    /// binding's resume path subtracts this to attribute epilogue time.
    pub static GC_FINISHED_ENTRY_NS: AtomicU64 = AtomicU64::new(0);
    /// Transition-gap accounting: time from the last in-pause packet
    /// completion to the next `on_last_parked` (park-convergence latency,
    /// the cost of the all-park barrier between bucket stages).
    pub static LAST_PKT_END_NS: AtomicU64 = AtomicU64::new(0);
    pub static TRANS_GAP_SUM_NS: AtomicU64 = AtomicU64::new(0);
    pub static TRANS_GAP_MAX_NS: AtomicU64 = AtomicU64::new(0);
    pub static TRANS_N: AtomicU64 = AtomicU64::new(0);
    /// Churn detector: `on_last_parked` invocations with NO packet executed
    /// since the previous invocation (the park/wake oscillation).
    pub static CHURN_N: AtomicU64 = AtomicU64::new(0);
    pub static LAST_SEEN_PKT_N: AtomicU64 = AtomicU64::new(0);
    /// Which find_more_work branch fired last: 1=designated 2=sentinel 3=buckets.
    pub static LAST_FIND_BRANCH: AtomicU64 = AtomicU64::new(0);
    /// Remaining churn-event log lines (global budget).
    pub static CHURN_LOG_BUDGET: AtomicU64 = AtomicU64::new(40);
    /// Root-scan anatomy (reset by the binding at pause start): splits the
    /// in-pause root work by class so the Init pause floor can be attributed.
    pub static ROOTS_MUT_NS: AtomicU64 = AtomicU64::new(0); // sum of ScanMutatorRoots packets
    pub static ROOTS_MUT_MAX_NS: AtomicU64 = AtomicU64::new(0);
    pub static ROOTS_MUT_N: AtomicU64 = AtomicU64::new(0);
    pub static ROOTS_VM_NS: AtomicU64 = AtomicU64::new(0); // ScanVMSpecificRoots
    pub static PREP_NS: AtomicU64 = AtomicU64::new(0); // global Prepare packet
    pub static PREP_MUT_NS: AtomicU64 = AtomicU64::new(0); // sum of PrepareMutator packets
    // CommonPlan::prepare sub-parts (immortal / LOS / nonmoving / base+vmspace)
    pub static PREP_IMM_NS: AtomicU64 = AtomicU64::new(0);
    pub static PREP_LOS_NS: AtomicU64 = AtomicU64::new(0);
    pub static PREP_NM_NS: AtomicU64 = AtomicU64::new(0);
    pub static PREP_BASE_NS: AtomicU64 = AtomicU64::new(0);
    /// Written by the binding: time inside `mmtk_scan_gcstack` walks and the
    /// number of task stacks walked during mutator root scanning.
    pub static STACKSCAN_NS: AtomicU64 = AtomicU64::new(0);
    pub static STACKSCAN_TASKS: AtomicU64 = AtomicU64::new(0);
    pub static STACKSCAN_SLOTS: AtomicU64 = AtomicU64::new(0);
    pub static TRIAGE_FREED: AtomicU64 = AtomicU64::new(0);
    pub static TRIAGE_POOLED: AtomicU64 = AtomicU64::new(0);
    pub static POOL_POPS: AtomicU64 = AtomicU64::new(0);
    pub static CLEAN_BLOCKS: AtomicU64 = AtomicU64::new(0);
    pub static REUSED_BLOCKS: AtomicU64 = AtomicU64::new(0);
    /// Census free-RUN length histogram (mixed blocks): buckets of
    /// contiguous non-epoch line runs, i.e. the holes future claims will
    /// see.  Buckets: 1, 2, 3-4, 5-8, 9-16, 17-32, 33+ lines.
    pub static FREE_RUN_HIST: [AtomicU64; 7] = [
        AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
        AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
    ];
    pub fn record_free_run(len: usize) {
        let b = match len {
            0 => return,
            1 => 0, 2 => 1, 3..=4 => 2, 5..=8 => 3, 9..=16 => 4, 17..=32 => 5, _ => 6,
        };
        FREE_RUN_HIST[b].fetch_add(1, Ordering::Relaxed);
    }
    pub static HOLE_CLAIMS: AtomicU64 = AtomicU64::new(0);
    pub static HOLE_LINES: AtomicU64 = AtomicU64::new(0);
    /// Monotone pause counter: bumped by the scheduler just before mutators
    /// resume from ANY pause.  Used by the allocator's thread-local claimed-
    /// hole cache to detect that a pause (and thus a possible remote
    /// allocator reset) happened since the holes were scanned.
    pub static PAUSE_EPOCH: AtomicU64 = AtomicU64::new(0);
    pub static CLAIM_NS: AtomicU64 = AtomicU64::new(0);
    pub static CLAIM_N: AtomicU64 = AtomicU64::new(0);
    pub static CLAIM_MAX_NS: AtomicU64 = AtomicU64::new(0);
    /// Nursery (minor) sweep results: blocks released / kept, lines freed.
    pub static NURSERY_SWEPT_BLOCKS: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    pub static NURSERY_KEPT_BLOCKS: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    pub static NURSERY_FREED_LINES: std::sync::atomic::AtomicUsize =
        std::sync::atomic::AtomicUsize::new(0);
    pub static PAUSE_PENDING: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
    /// Env-gated (MMTK_TRACE_GUARDS) validity checks on traced values:
    /// report-and-skip refs outside every MMTk space instead of chasing them.
    /// Diagnostic only -- costs an SFT lookup per traced edge when enabled.
    pub fn trace_guards_enabled() -> bool {
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("MMTK_TRACE_GUARDS").is_some())
    }
    /// Env-gated (MMTK_PACER_TRACE) tracing of GC-trigger/pacing decisions.
    pub fn pacer_trace_enabled() -> bool {
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("MMTK_PACER_TRACE").is_some())
    }
    /// MUTATOR-SHOULDERED GC WORK (MMTK_MUTGC): cumulative time the mutator
    /// thread spends doing GC work outside pauses -- SATB whole-object
    /// capture, slot-precise capture, and lazy triage (TRIAGE_* above).
    /// Histogram buckets: <1us, <10us, <100us, <1ms, <10ms, >=10ms.
    pub static MUT_SATB_NS: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SATB_N: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SATB_MAX_NS: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SATB_SLOTS: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SATB_SLOTS_MAX: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SATB_HIST: [AtomicU64; 6] = [
        AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
        AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0),
    ];
    /// Per-requester counts of concurrent-cycle requests (pacer forensics).
    pub static PACER_REQ_MINOR: AtomicU64 = AtomicU64::new(0);
    pub static PACER_REQ_OVERGOAL: AtomicU64 = AtomicU64::new(0);
    pub static PACER_REQ_PROMO: AtomicU64 = AtomicU64::new(0);
    pub static PACER_REQ_HEADROOM: AtomicU64 = AtomicU64::new(0);
    pub static PACER_REQ_FLOAT: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SLOTCAP_NS: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SLOTCAP_N: AtomicU64 = AtomicU64::new(0);
    pub static MUT_SLOTCAP_MAX_NS: AtomicU64 = AtomicU64::new(0);
    pub fn mutgc_enabled() -> bool {
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| {
            let on = std::env::var_os("MMTK_MUTGC").is_some();
            if on {
                unsafe { libc::atexit(print_mutgc_summary) };
            }
            on
        })
    }
    /// Outlier threshold for per-capture [satb-outlier] prints (us).
    pub fn mutgc_outlier_ns() -> u64 {
        static V: OnceLock<u64> = OnceLock::new();
        *V.get_or_init(|| {
            std::env::var("MMTK_MUTGC_OUTLIER_US")
                .ok()
                .and_then(|v| v.parse::<u64>().ok())
                .unwrap_or(100)
                * 1000
        })
    }
    pub fn record_satb_capture(ns: u64, slots: u64) {
        MUT_SATB_NS.fetch_add(ns, Ordering::Relaxed);
        MUT_SATB_N.fetch_add(1, Ordering::Relaxed);
        MUT_SATB_SLOTS.fetch_add(slots, Ordering::Relaxed);
        record_max(&MUT_SATB_MAX_NS, ns);
        record_max(&MUT_SATB_SLOTS_MAX, slots);
        let b = match ns {
            0..=999 => 0,
            1_000..=9_999 => 1,
            10_000..=99_999 => 2,
            100_000..=999_999 => 3,
            1_000_000..=9_999_999 => 4,
            _ => 5,
        };
        MUT_SATB_HIST[b].fetch_add(1, Ordering::Relaxed);
    }
    extern "C" fn print_mutgc_summary() {
        let ms = |v: u64| v as f64 / 1e6;
        let h: Vec<u64> = MUT_SATB_HIST.iter().map(|x| x.load(Ordering::Relaxed)).collect();
        eprintln!(
            "[mutgc] satb_capture: n={} total={:.1}ms max={:.3}ms slots={} slots_max={} hist(<1us,<10us,<100us,<1ms,<10ms,>=10ms)={:?}",
            MUT_SATB_N.load(Ordering::Relaxed),
            ms(MUT_SATB_NS.load(Ordering::Relaxed)),
            ms(MUT_SATB_MAX_NS.load(Ordering::Relaxed)),
            MUT_SATB_SLOTS.load(Ordering::Relaxed),
            MUT_SATB_SLOTS_MAX.load(Ordering::Relaxed),
            h,
        );
        eprintln!(
            "[mutgc] slot_capture: n={} total={:.1}ms max={:.3}ms",
            MUT_SLOTCAP_N.load(Ordering::Relaxed),
            ms(MUT_SLOTCAP_NS.load(Ordering::Relaxed)),
            ms(MUT_SLOTCAP_MAX_NS.load(Ordering::Relaxed)),
        );
        eprintln!(
            "[mutgc] lazy_triage: chunks={} total={:.1}ms max={:.3}ms freed_blk={} pooled_blk={}",
            TRIAGE_CHUNKS.load(Ordering::Relaxed),
            ms(TRIAGE_NS_TOTAL.load(Ordering::Relaxed)),
            ms(TRIAGE_MAX_NS.load(Ordering::Relaxed)),
            TRIAGE_FREED.load(Ordering::Relaxed),
            TRIAGE_POOLED.load(Ordering::Relaxed),
        );
        eprintln!(
            "[mutgc] claim_path: n={} total={:.1}ms max={:.3}ms",
            CLAIM_N.load(Ordering::Relaxed),
            ms(CLAIM_NS.load(Ordering::Relaxed)),
            ms(CLAIM_MAX_NS.load(Ordering::Relaxed)),
        );
        let h: Vec<u64> = FREE_RUN_HIST.iter().map(|x| x.load(Ordering::Relaxed)).collect();
        eprintln!("[mutgc] census_free_runs(1,2,3-4,5-8,9-16,17-32,33+)={:?}", h);
        let hc = HOLE_CLAIMS.load(Ordering::Relaxed);
        let hl = HOLE_LINES.load(Ordering::Relaxed);
        eprintln!(
            "[mutgc] holes: claims={} lines={} avg_run_bytes={} clean_blk={} reused_blk={}",
            hc, hl,
            if hc > 0 { hl * 256 / hc } else { 0 },
            CLEAN_BLOCKS.load(Ordering::Relaxed),
            REUSED_BLOCKS.load(Ordering::Relaxed),
        );
    }
    /// Env-gated (MMTK_PAUSE_PKT_HIST) per-pause packet-type histogram:
    /// counts and total ns per packet type executed while a pause is
    /// active.  Dumped and cleared at pause end by the binding.
    pub static PKT_HIST: std::sync::Mutex<Vec<(&'static str, u64, u64)>> =
        std::sync::Mutex::new(Vec::new());
    pub fn pkt_hist_enabled() -> bool {
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("MMTK_PAUSE_PKT_HIST").is_some())
    }
    pub fn pkt_hist_record(name: &'static str, ns: u64) {
        let mut h = PKT_HIST.lock().unwrap();
        for e in h.iter_mut() {
            if e.0 == name {
                e.1 += 1;
                e.2 += ns;
                return;
            }
        }
        h.push((name, 1, ns));
    }
    pub fn pkt_hist_dump() {
        let mut h = PKT_HIST.lock().unwrap();
        if h.is_empty() {
            return;
        }
        h.sort_by_key(|e| std::cmp::Reverse(e.1));
        let line: Vec<String> = h
            .iter()
            .map(|(n, c, ns)| format!("{}:n={},ms={:.1}", n, c, *ns as f64 / 1e6))
            .collect();
        eprintln!("[pkt-hist] {}", line.join(" "));
        h.clear();
    }
    pub fn record_max(s: &AtomicU64, v: u64) {
        let mut c = s.load(Ordering::Relaxed);
        while v > c {
            match s.compare_exchange_weak(c, v, Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => break, Err(x) => c = x,
            }
        }
    }
    pub fn reset() {
        for s in [&REQUEST_NS, &LAT_TOTAL_NS, &LAT_MAX_NS, &LAT_COUNT, &PKTS_TOTAL,
                  &PKT_NS_TOTAL, &PARK_EVENTS, &BUSY_AT_REQ_TOTAL] { s.store(0, Ordering::SeqCst); }
        PKTS_SINCE_REQ.store(0, Ordering::SeqCst);
        PKT_MAX_IN_WIN_NS.store(0, Ordering::SeqCst);
        PKT_SUM_IN_WIN_NS.store(0, Ordering::SeqCst);
        PKT_MAX_ANY_NS.store(0, Ordering::SeqCst);
        REQ_PENDING.store(false, Ordering::SeqCst);
        SELF_TRIGGERED.store(0, Ordering::SeqCst);
        NOREQ_PARKS.store(0, Ordering::SeqCst);
        NOREQ_CONCURRENT_SOME.store(0, Ordering::SeqCst);
        NOREQ_CM_ACTIVE.store(0, Ordering::SeqCst);
        SWEEP_NS.store(0, Ordering::SeqCst);
        SWEEP_PKTS.store(0, Ordering::SeqCst);
        SWEEP_OUTSTANDING.store(0, Ordering::SeqCst);
        TRIAGE_MAX_NS.store(0, Ordering::SeqCst);
        TRIAGE_NS_TOTAL.store(0, Ordering::SeqCst);
        UNLOG_MAX_NS.store(0, Ordering::SeqCst);
    }
}
pub mod util;
pub mod vm;

pub use crate::plan::{
    AllocationSemantics, BarrierSelector, Mutator, MutatorContext, ObjectQueue, Plan,
};
