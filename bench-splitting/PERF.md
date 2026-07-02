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
