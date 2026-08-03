# Plan: Generational ConcurrentImmix (sticky nursery + concurrent SATB majors)

Direction agreed 2026-08-03: start from the working generational side
(StickyImmix semantics) and add concurrency to the major cycle, rather than
bolting a nursery onto ConcurrentImmix. Phase 1 forbids minors while a major
is marking.

## 1. Goal and success criteria

Combine StickyImmix's mutator performance (cache-tier reuse locality,
near-zero mark work per collection) with ConcurrentImmix's pause profile
(sub-0.2ms Init/Final, no synchronous full collections).

Measured acceptance criteria (worst-case pure-allocation loop, 30M iters,
default configuration, the `passes.jl` harness):

| Criterion | Target | Baseline today |
|---|---|---|
| Steady-state wall per pass | <= 1.35s (Sticky 1.24-1.30 +10%) | ConcImmix 1.7-2.0s |
| Mutator IPC | >= 3.3 | ConcImmix 2.5, Sticky 3.67 |
| Minor pause p99 | <= 0.5ms | n/a (Sticky ~sub-ms STW) |
| Major Init/Final mean | <= 0.2ms (unchanged) | 0.05-0.15ms |
| Trigger blocking (block_for_gc) | 0 in steady state | 0 (preserved) |
| Footprint | <= 3x live + nursery | bounded |
| Full make gate + 30x REPLExt stress | green | green |

## 2. Architecture

### 2.1 Collection kinds
- **Minor (nursery) GC**: STW pause (new `Pause::Nursery`), traces roots +
  remset, terminates at marked (old) objects — StickyImmix's nursery trace.
  Nursery = objects allocated since the last collection. In-place, no
  copying (MMTK_MOVING=0). Nursery line sweep runs *inside* the pause on
  workers (nursery is small; this is also the locality mechanism: swept
  lines feed the allocator immediately, cache-warm — the measured L2/L3
  tier of stock/Sticky).
- **Major GC**: the existing concurrent SATB cycle (InitialMark ->
  concurrent mark -> FinalMark), whole heap, with the current pacer/goal
  trigger, lazy sweep, and pause machinery unchanged.

### 2.2 Barrier unification (the crux)
Both plans already use the same mechanism: `ObjectBarrier` gated on the
unlog bit, logging the mutated object into the modbuf. Unify the semantics:

- Bit ARMED = "old and unmutated since last drain".
- Fastpath: always on (unlog-bit check; the marking-gated fastpath from the
  WB-gate campaign is surrendered — its win was idle-window-only, and
  stock/Sticky pay the always-on check everywhere).
- Between majors: modbuf = **remset** (old objects mutated since last
  minor); minors drain it as additional roots, then re-arm drained objects.
- During major marking: modbuf = **SATB log** (same packets,
  `ProcessModBufSATB`), as today.
- Phase 1 has a single consumer at any time (minors forbidden during
  marking). Transition soundness: remset entries pending at InitialMark are
  valid SATB work (rescanning a mutated old object is conservative).
- Promotion is free: FinalMark's existing deferred full re-arm
  (`UnlogBitsChunk BulkSet` + `SetCommonPlanUnlogBits`) IS the "everything
  surviving a major becomes old" step. Minor survivors are armed by the
  existing `unlog_traced_object` trace-time re-arm.

### 2.3 Mark-bit lifecycle (decision point)
Sticky semantics require survivor marks to PERSIST between collections (the
old-set indicator minors terminate on). Our current major clears mark bits
in deferred post-FinalMark packets — that would erase the old set during
the window where minors need it.

Options:
- (a) In-pause clear at InitialMark: restores ~60-170us to Init (the cost
  removed by b26244cfc8). Simple, known-sound.
- (b) **Two alternating mark planes** (recommended): duplicate the mark-bit
  side metadata; InitialMark flips the active plane (O(1)); the old plane
  (still holding the pre-major old set — unused once the major completes)
  is background-zeroed after FinalMark for reuse next major. Preserves the
  O(1) Init pause. Cost: 2x mark metadata (1/128 of heap doubled) plus a
  plane indirection in `attempt_mark`/`is_marked`.
- Decide by measurement in Phase 1: implement (a) first (trivial), promote
  to (b) only if Init pause regression matters.

### 2.4 Allocate-black vs nursery (Phase 1 stance)
Objects allocated during a major's marking are black (uncollectable until
the next major) and will be treated as old by the first post-major minors
without ever surviving a minor. Accepted as float: the next major reclaims
them. Documented footprint cost proportional to allocation during marking
(~alloc_rate x cycle_time). Phase 3 revisits with allocation-epoch tags.

### 2.5 Line marks and sweeping
- Minors: sticky-standard eager nursery line sweep in-pause; swept lines go
  directly to the allocator's recyclable supply (warm reuse loop; nursery
  sized cache-scale).
- Majors: existing lazy sweep (unswept lists, allocation-paid triage,
  two-epoch predicate) unchanged. Line-epoch interaction: minors bump the
  line mark state per collection exactly as Sticky does; the major triage
  predicate already tolerates arbitrary intermediate states via the
  cur/unavail scheme — audit in 1.4, this is the most likely place for a
  subtle hole.

### 2.6 Triggers
- Minor: nursery-bytes threshold, default min(32MB, goal/8), later
  cache-aware autotuning. Async request (minors are cheap; the existing
  request-and-continue machinery applies; blocking never required since a
  minor cannot exhaust the heap).
- Major: existing pacer, with one input improvement for free — live
  estimate after a minor is far more accurate than `live_bytes_prev`, so
  feed `live_pages_estimate` from post-minor accounting.
- Interlocks: skip/defer minors while `concurrent_marking_in_progress()`
  (nursery grows; hasten FinalMark if it grows past a bound). Pause
  serialization for minor-vs-major initiation already exists (single
  scheduler goal).

## 3. Work plan

### Phase 0: scaffolding (2-3 days)
- Evolve ConcurrentImmix in place (no new plan enum) behind the existing
  build flag; add `Pause::Nursery` and plumb kind counters
  (`mmtk_stw_kind_n` slot 4) + harness support.
- Record baselines on the current tip (passes/tailm/val/trigger-churn/MT +
  the per-thread fill-source measurement) for the comparison table.

### Phase 1: minors outside marking (1.5-2 weeks)
1.1 Always-on barrier: remove the marking gate from the WB fastpaths
    (C fastpath, LLVM lowering, jl_gc_queue_root gates); keep
    MMTK_SATB_MARKING_ACTIVE only where SATB-vs-remset drain behavior
    differs. A/B the mutator cost on the benchmark suite (expected ~0 on
    the alloc loop; measure a pointer-write-heavy workload too).
1.2 `Pause::Nursery` schedule: StopMutators (flush mutators -> modbuf
    remset packets) -> eager root scan (STW stack walks — the existing
    pre-(b26244) path, correct for minors) -> nursery closure -> in-pause
    nursery line sweep -> release. Reuse `trace_object_nursery` /
    `GenerationalPlanExt` from the sticky implementation.
1.3 Mark persistence: option (a) in-pause Init clear; measure; decide on
    plane scheme (b).
1.4 Line-state audit: minors bumping line epochs vs major triage predicate
    vs claim-time `bulk_set_line_mark_states`. Extend the unlog/mark audit
    oracle: at every minor start, armed-set == old-set (sampled); at every
    Init, current invariants hold. Run under MMTK_TRACE_GUARDS in stress.
1.5 Promotion arming via `unlog_traced_object` on the nursery trace path;
    verify with the audit oracle.
1.6 Minor trigger + interlocks (2.6).
1.7 Validation gate: full make, 30x REPLExt (+ small-heap variant),
    passes/tailm/val/MT/trigger-churn matrix, hard-cap 320MB, guards run.

Exit criteria: wall <= 1.5s on the benchmark (partial win expected already:
minors give warm line reuse), zero blocking, all gates green, minor p99
under 1ms (tuning to 0.5ms is Phase 2).

### Phase 2: integration and performance (1.5-2 weeks)
2.1 Pacer: post-minor live feeding; major goal on old-generation growth;
    verify goal stability (the [pacer] trace).
2.2 Minor pause tuning with pause-anatomy instrumentation (root-scan cost
    dominates: task-count scaling applies to minors — reuse the roots.jl
    grid; consider remset-only stack treatment later).
2.3 Nursery size sweep (locality vs pause length); document default.
2.4 Full comparison table vs stock/Sticky/old-ConcurrentImmix, including
    fill-source counters (expect L3-tier: DRAM fills/Ginstr ~1.7-2.0M,
    L3 fills restored).
2.5 Cleanup: strip/gate remaining diagnostics; commit series with the
    validation evidence.

### Phase 3 (separate go/no-go): minors during concurrent marking
Only if Phase 2 data shows the nursery-growth-during-marking window hurts
(long majors x high allocation): modbuf dual-consumer protocol,
allocation-epoch tags for allocate-black vs nursery, promotion rules during
marking. G1 precedent exists; research-flavored; 2-4 weeks. The marking-
throughput track (below) shrinks the window and may make this unnecessary.

### Parallel track (independent of all phases): marking throughput
The visit_slot/SFT/side-metadata stack runs ~50MB/s/worker; majors at
~130ms dominate the minors-forbidden window and the major reuse distance.
Any improvement here compounds with the generational work and is
independently schedulable.

## 4. Risks and mitigations
- **Barrier/metadata invariant holes** (4 found in the WB-gate campaign,
  1 in the trigger campaign): every phase lands behind the full gate +
  REPLExt stress with timeout-wrapped loops; audit oracles extended first,
  features second. Budget: validation ~= coding time.
- **Disable-window contract**: pauses are already gated
  (is_collection_enabled + Dekker request handshake); minors must use the
  same gates (they do, via the shared initiation path). Verified by the
  pacer-block trace.
- **Line-epoch scheme collision** (2.5): highest technical risk; the audit
  oracle in 1.4 is built BEFORE the nursery sweep lands.
- **Upstream drift**: os/concurrent-immix was rebased + 50 commits; this
  work deepens the fork. Accepted: vendored tree is the working base;
  upstreaming discussions after Phase 2 evidence exists.

## 5. Estimates
Phase 0: 2-3 days. Phase 1: 1.5-2 weeks. Phase 2: 1.5-2 weeks.
Phase 3: separate decision, 2-4 weeks if taken.
Total to acceptance criteria: ~4-5 weeks of this campaign's cadence,
validation-dominated.
