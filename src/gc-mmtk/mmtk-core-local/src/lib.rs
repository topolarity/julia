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
