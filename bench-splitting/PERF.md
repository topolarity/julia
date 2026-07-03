# PMU attribution of the super-linear region-boundary cost

Self-contained instructions for a machine with full perf/PMU support.
Context and all prior evidence: see NOTES.md in this directory (section
"COMPLETE PICTURE" and the boundary-tax measurements).

## The question

The JuliaFunctionSplitting pass splits oversized functions into region
functions called from residual glue. With SLP disabled everywhere (so codegen
is identical modulo splitting machinery), the runtime cost per region
boundary on a call-free branchy float benchmark is:

| function size | region size ~400 | region size ~1600 |
|---|---|---|
| 64k stmts  (324 / 81 boundaries)   | ~10 ns/boundary | ~8 ns/boundary |
| 256k stmts (1284 / 321 boundaries) | ~35 ns/boundary | ~14 ns/boundary |

The unsplit versions of the same functions are size-insensitive
(0.128 ns/executed-op at both sizes), so straight-line prefetch hides the
code-footprint entirely; only the split versions degrade, and super-linearly.

Exact post-opt module instruction counts (SLP off; marshalling adds a
constant ~118 instructions/boundary; ~10-12 bytes/inst of machine code):

| config | post-opt insts | est. code | runtime | ns/boundary |
|---|---|---|---|---|
| off 64k    | 147,905 | ~1.6 MB | 4.20us  | — |
| c400 64k   | 185,884 | ~2.0 MB | 7.77us  | 11.0 |
| off 256k   | 589,505 | ~6.5 MB | 16.37us | — |
| c1600 256k | 628,941 | ~6.9 MB | 21-24us | 14-24 |
| c400 256k  | 741,231 | ~8.2 MB | 60.9us  | 34.7 |

Note the unsplit 6.5 MB streams at full speed, and the 2.0 MB split config
already exceeds the 1.25 MiB per-core L2 yet costs only 11ns/boundary — so a
hard L2 threshold is too simple. The smooth footprint-vs-cost relation is
consistent with partial L2 residency (LRU fraction shrinking from ~60% at
2 MB to ~15% at 8 MB) with misses concentrated at prefetch-breaking region
entries, but that is exactly what the counters must confirm or refute.

Working hypothesis: per-boundary cost = ~10ns marshalling core (call/ret,
~10 stack-arg pushes, vzeroupper pair, 8x store-to-load round trip, exit
selector) + a fetch-stall term that switches on when the per-iteration
instruction footprint exceeds the per-core L2 (1.25 MiB on the original
machine, i7-12700H), because every region call/ret breaks the sequential
prefetch stream. Candidate mechanisms the counters must separate:

- A: L1i/L2 code misses at region entry (footprint residency)
- B: iTLB/STLB walks (page-count effect, ~1250 code pages at 256k/c400)
- C: BTB capacity / front-end re-steers (per-branch-site effect;
     note the JIT emits region calls as movabs+`call rax`, i.e. indirect)

Behavioral evidence gathered without PMU (see NOTES.md addendum 2):
per-boundary cost is monotone in total code footprint at fixed boundary
structure (6.9/7.1/7.7/8.2 MB -> ~14-24/18.8/23.4/34.7 ns), and the
indirect-site-count (C) hypothesis is REFUTED behaviorally (c565: 914 sites,
7.1MB, 18.8ns vs c800: 711 sites, 7.7MB, 23.4ns — ordering follows footprint,
not sites). Region calls ARE all indirect (movabs+call rax; JIT is
CodeModel::Large, Medium crashes on out-of-range data relocations), so C is
still worth one look, but A vs B is the main question.

Static candidates already ELIMINATED by asm inspection (do not re-chase):
the per-boundary instruction sequence is identical at both scales (~118
insts/boundary); root frames are tiny (spill structs are sunk into parent
frames, data working set ~1KB/parent, L1-resident); the one structural
difference is hierarchy depth (2 levels at 64k/c400 vs 3 at 256k/c400),
which affects only ~1/16 of transitions and bounds at ~10%, not 3x.

## Setup

1. Build this branch of julia (`make -j`). The pass and the benchmark
   harness are in-tree; nothing else is needed for the synthetic benchmarks
   (`envs/` setup via setup_envs.jl is only for the ReverseDiff composite
   benchmarks, not required here).
2. Check `perf stat -e L1-icache-load-misses true` works.
3. Pick a P-core and set `CORE` (default 2). Disable turbo if you want
   stable per-cycle numbers (optional; rates vs iters/sec normalize it out).

## The matrix

For EVENTS start portable, then Alder-Lake-specific:

    EV1="task-clock,cycles,instructions,branches,branch-misses,L1-icache-load-misses,iTLB-load-misses"
    EV2="frontend_retired.l1i_miss,frontend_retired.l2_miss,frontend_retired.itlb_miss,frontend_retired.stlb_miss,baclears.any,idq_uops_not_delivered.core"

Run (each ~35s):

    for S in 64000 256000; do
      for CH in off 400 1600; do
        bash perf_one.sh $S $CH "$EV1" | tee perf_${S}_${CH}_ev1.txt
        bash perf_one.sh $S $CH "$EV2" | tee perf_${S}_${CH}_ev2.txt
      done
    done

Optionally also topdown: `perf stat -M tma_frontend_bound,tma_fetch_latency -p ...`
via EVENTS="-M tma_frontend_bound" (adjust perf_one.sh if -M syntax differs).

## Normalization and interpretation

Each run prints `PERFDONE iters=N secs=T` (harness iteration rate) and perf
prints counters over its attach window. Compute per-boundary deltas:

    boundaries(S, CH): 64000/400 -> 324, 64000/1600 -> 81,
                       256000/400 -> 1284, 256000/1600 -> 321
    per_boundary(X) = (X_split/sec - X_off/sec) / (iters/sec * boundaries)

Predictions:
- If A (code residency): frontend_retired.l2_miss (and L1-icache-load-misses)
  per boundary jumps to O(1-3) at 256k/c400 but stays ~0 at 64k/c400;
  iTLB flat; expect ~1.5-2 misses/boundary x ~15-20ns L3 latency ~ +25ns.
- If B (iTLB): itlb/stlb misses per boundary elevated at 256k (~0.5-1),
  page-walk latency ~20-30ns each; L2-miss counters comparatively flat.
- If C (BTB): baclears.any / branch-misses per boundary elevated at 256k
  even though branch-site count per boundary is constant; L1i/iTLB flat.
- The ~10ns core should appear in all configs as extra instructions
  (~35/boundary) + idq_uops_not_delivered without misses.

Also worth one extra pair while you have counters (secondary question,
NOTES.md "Task 1/2"): unsplit straight-line 64k with SLP on vs off
(GEN=straight, LABEL as you like, JULIA_LLVM_ARGS="" vs
"-vectorize-slp=false") — confirm the 2-wide SLP code (2x instructions) is
front-end bound (tma_frontend_bound share), which is why it runs 2x slower
than scalar.

## Reporting back

The numbers that matter, per (S, CH): iters/sec, and per-boundary rates for
each event. A short table is enough to pick between A/B/C, or to conclude a
mix. If none of the three moves, the residual suspects are RSB behavior and
store-forwarding stalls (measure ld_blocks.store_forward, and
frontend_retired.ms_flows for good measure).

## RESULTS (2026-07-02, AMD EPYC 9354 / Zen 4, ~3.2 GHz, 32K L1i / 1M L2 / 32M L3-per-CCX)

Measured on a different microarch than the question was posed on (Zen 4, not
ADL); event mapping: frontend_retired.l2_miss -> ic_cache_fill_sys (L1i
demand fills sourced beyond L2), l1i_miss -> ic_cache_fill_l2, itlb/stlb ->
bp_l1_tlb_miss_l2_tlb_hit / bp_l1_tlb_miss_l2_tlb_miss.all, baclears ->
bp_de_redirect, idq_uops_not_delivered ->
de_no_dispatch_per_slot.no_ops_from_frontend. Only 5 hw counters free (NMI
watchdog holds the 6th; no sudo), so 4 groups of <=5 events were attached
back-to-back to ONE julia process per config (perf_matrix.sh; per-boundary
normalization in perf_analyze.jl; raw output in perfout/). Harness fix
required first: gen_axes.jl's PERFMODE loop hit top-level soft scope
(`it += 1` -> unbound local, process died ~2s after PERFREADY) -> now
`global it += 1`. Cross-check: measured cycle deltas match wall-time deltas
within 5% in all four split cells.

The boundary tax is larger on this machine (ns/boundary: 20/8 at 64k
c400/c1600, 81/170 at 256k) but the attribution is clean. Per-boundary
deltas (split minus off, divided by boundary count):

| event per boundary       | 64k c400 | 64k c1600 | 256k c400 | 256k c1600 |
|---|---|---|---|---|
| ns (wall)                | 20.1  | 7.8   | 81.1  | 170.2 |
| cycles                   | 61.7  | 18.6  | 245.9 | 533.3 |
| instructions             | 155.9 | 116.7 | 112.2 | 139.0 |
| ic_cache_fill_l2         | 15.7  | 19.1  | -5.4  | -20.9 |
| ic_cache_fill_sys        | 1.7   | 0.1   | 25.4  | 65.6  |
| iTLB full walks          | 0.02  | 0.02  | 0.40  | 1.52  |
| branch-misses            | 0.23  | 0.02  | 5.1   | 10.0  |
| bp_de_redirect           | 0.17  | 0.01  | 5.6   | 9.1   |
| FE-starved slots (/6=cyc)| 470   | 56    | 1709  | 3968  |

IPC: unsplit 2.51 (64k) / 2.34 (256k); split 64k c400 2.52 (unchanged!);
split 256k collapses to 0.80 / 0.87 — the added time at 256k is entirely
front-end starvation (starved-slot cycles ~= the whole cycle delta).

Verdict: **A dominant, C secondary, B refuted.**

- The ~10ns core is confirmed and is ALL of the 64k cost: at 64k the split
  config runs at the SAME IPC as unsplit — the tax is exactly the ~118-156
  marshalling instructions/boundary executing at full throughput, with no
  stall signature (sys fills ~0, starved slots ~78 cyc/b at c400, ~9 at
  c1600). ~20ns/b here vs ~10-11 on ADL is clock + uarch, not structure.
- A (code residency): ic_cache_fill_sys jumps 0-2 -> 25-66/boundary at 256k,
  the predicted signature, at an effective ~8-10 cycles per demand fill
  after overlap (Delta-cycles/Delta-sys-fills = 9.7 at c400, 8.1 at c1600).
  Key contrast: unsplit-256k already streams 5.5k sys fills/iter at IPC
  2.34 — sequential prefetch hides L3-sourced code fetch completely;
  splitting both multiplies demand fills 3-7x and exposes them (region
  call/ret breaks the fetch-ahead stream at every entry/exit).
- C (predictor capacity) is real but secondary: branch-misses and decode
  resteers go from ~0 to 5-10/boundary at 256k with identical per-boundary
  branch structure -> BTB/indirect-target/RAS capacity (the movabs+call rax
  boundary calls have 1284 distinct targets at 256k/c400). Upper bound
  ~75-150 cyc/b at ~15 cyc each, and it overlaps the fetch misses.
- B (iTLB): <=1.5 full walks/boundary at worst; L1->L2-iTLB hits flat or
  negative. <=10-15% of the cycle delta even priced at full walk latency.

Reframing that matters for the pass: per-boundary normalization misleads at
256k — c1600 is WORSE per boundary here (170 vs 81 ns) yet better per
iteration (+54.6us vs +104.2us vs off 22.3us). The capacity term scales
with code footprint streamed per iteration (demand sys fills/iter: 32.6k at
c400 = 8.2MB footprint vs 21.1k at c1600 = 6.9MB), not with boundary count.
NOTES.md's "runtime of once-through code tracks final code size, not
boundary count" is confirmed dynamically:

    penalty/iter ~= marshalling_insts/IPC + ~9 cyc x demand_code_fills
                    (+ mispredict term), fills ~ footprint once >> L2

Boundary count enters mainly by inflating the footprint (+118 insts x 1284
boundaries = +151k insts at 256k/c400), which argues again for fewer,
larger regions on call-free code — now with a mechanism attached.

Secondary question (straight-64k SLP on vs off): does NOT reproduce on
Zen 4. Runtime identical (8.63 vs 8.65 us, 0.135 ns/op both, i.e. at the
FMA bound); SLP-on is 74% backend-stalled, only 3.8% FE-starved, running
from the legacy decoder (op-cache miss, 0 loop buffer) at IPC 1.03; scalar
runs 2x the instructions at IPC 2.01 in the same wall time. The ADL
"2-wide SLP is a 2x front-end-bound pessimization" is machine-specific;
Zen 4's decode path keeps up with the L2-resident ~650KB stream. (SLP's
~cubic COMPILE cost does reproduce: 39.5s vs 14.1s total compile, LLVM
share 27.3s vs 1.0s.)

## FOLLOW-UP: does region sizing alone obviate the CodeModel change?

Decides whether the pass needs Medium+PIC or whether capacity-aware region
sizing suffices under the stock Large model. The open cell: does the Large
model's per-boundary cost (~170ns at 256k/c1600 here) shrink as regions
grow, or does blind-entry fetch + mispredict-flush impose a per-entry floor?

Runs (stock jitlayers = CodeModel::Large, SLP off as before; ~35s each):

    for CH in 1600 3200 6400 12800 off; do
      bash perf_one.sh 256000 $CH "$EV1" | tee perf_L_256000_${CH}_ev1.txt
      bash perf_one.sh 256000 $CH "$EV2" | tee perf_L_256000_${CH}_ev2.txt
    done

(c1600/off re-baselined in-session for comparability; realized region counts
are ~321/160/80/40 — verify with -julia-split-time if in doubt. 2 reps if
time permits; single runs were reproducible to ~2% on this harness here.)

Interpretation:
- If penalty/iter keeps falling roughly with boundary count (c12800 within
  ~10% of off), sizing alone suffices: the pass scales its region target
  with function size and Medium+PIC becomes an independent JIT-wide track
  (it likely still pays: every JIT'd specsig call is movabs+call rax today).
- If per-boundary cost floors at >=~150ns (penalty stuck around +6-8us at
  c6400 and beyond), the Large model has a blind-entry cost that sizing
  cannot amortize on this uarch, and Medium+PIC (or equivalent direct-call
  emission) is required for acceptable split-code runtime on call-free code.
- Optionally run the same sweep under Medium+PIC for the paired curve; the
  delta curve directly prices the CodeModel change per region size.

## RESULTS: sizing-vs-CodeModel (2026-07-03, same Zen 4 box, perf_matrix.sh)

Realized region counts at 256k (verified -julia-split-time on this tree):
c1600/3200/6400/12800 -> 356/183/93/47 (not the 321/160/80/40 estimates;
median realized sizes match targets: 1633/3214/6409/12826).

Penalty per iteration vs off (raw in perfout-sizes-large/ and
perfout-sizes-medium/; off baselines 22.7us (Large) / 24.7us (Medium+PIC),
within the known cross-process band):

| penalty us/iter (ns/boundary) | c1600 | c3200 | c6400 | c12800 |
|---|---|---|---|---|
| Large (stock)      | +53.3 (150) | +24.2 (132) | +6.6 (71) | +4.8 (102) |
| Medium+PIC (direct)| +14.6 (41)  | +5.3 (29)   | +4.5 (48) | +6.4 (136) |

Decision: **sizing alone suffices under stock Large — no per-entry floor —
but it needs ~2x larger regions to reach the same plateau** (Large converges
at c6400-12800 to the same +4.5-6.5us both models bottom out at; Medium+PIC
is already there at c3200). The Large collapse is predictor-capacity relief,
visible in the counters: branch-misses/iter 3182 -> 958 -> 159 -> 103 and
bp_de_redirect/iter 2893 -> 557 -> 100 -> 79 across c1600 -> c12800 — once
only ~93-47 indirect sites remain, the BTB/indirect predictor holds them
even under Large, fetch-ahead resumes, and the demand-fill term shrinks
(ic_cache_fill_sys/iter 25.1k -> 10.4k). Per-boundary cost is NOT constant
in region size (150 -> 71 -> 102 ns/b), reconfirming that the capacity term
scales with footprint/predictor pressure, not boundary count; the c12800
per-boundary upticks in both models are small absolute penalties (+4.8/6.4us)
divided by very few (47) boundaries.

For the pass: scale the region target with total function size so the
realized boundary-site count stays O(BTB) — ~100 sites was enough here even
with fully indirect calls. Medium+PIC (codemodel-medium-pic.patch, verified
working: direct rel32 calls, movabs count 0, identical results, smoke tests
pass; Static+Medium is NOT viable — R_X86_64_32S jump-table relocs assume
low 2GB) remains an independent JIT-wide track: it halves the region size
needed and would also de-indirect every JIT specsig call, but this pass no
longer depends on it. Anomaly flagged, not chased: the Medium c12800 EVA
window measured 87.5k insts/iter (~half of Large's 172.6k at identical IR)
at consistent cycles/iter — single-window artifact suspected; runtime for
that cell is PERFDONE-derived and solid.

## RESULTS: software code prefetch — REFUTED (2026-07-03)

-julia-split-prefetch-lines=N (EXPERIMENT flag in the pass, default 0):
before each region call, prefetcht1 the first N 64B lines of the NEXT
region's code (lookahead: issued before call k, covering region k+1, so
region k's execution overlaps the fills; x86 cannot prefetch into L1i, so
this targets the unified L2). Verified in asm (prefetcht1 [rip+...]).
On the Medium+PIC build at 256k:

  c400:  N=0 111.8us, N=4 114.5, N=8 114.9, N=16 112.5, N=32 118.6
  c1600: N=0 34.1us,  N=8 38.7,  N=32 41.3   (13-21% REGRESSION)

The counters (perfout-pf/, c400 N=32 vs N=0) show the prefetches DID land:
ic_cache_fill_l2/iter 921 -> 21,056 and ic_cache_fill_sys/iter 38,075 ->
25,571 (a third of from-L3 code fills converted to from-L2), instructions
+41k/iter (exactly the added prefetches) — and cycles/iter unchanged
(383k -> 392k). Conclusion: where fetch-ahead is broken (BTB overflow at
c400), the serialization is resteer-restart, not fill-source latency —
cheaper fills buy nothing; where fetch-ahead works (c1600), hardware
prefetch already covers it and the extra instructions + pollution are pure
overhead. Software code prefetch is not a lever for this pass on this
uarch; the levers remain (in order) region sizing and direct calls.
