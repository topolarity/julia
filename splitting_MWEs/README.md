# Function-splitting MWEs

Workloads that isolate each super-linear compile-time behavior the
`FunctionSplittingPass` / `BasicBlockSplittingPass` (src/llvm-function-splitting.cpp)
exist to bound, used to tune the pass's default thresholds. Each stresses a
distinct pass/mechanism. Compile times below are from the tuning campaign
(Zen 4, assertions build); treat as relative shapes, not absolutes.

## The tuned defaults and what each cap models

| knob | default | bounds | driven by |
|---|---|---|---|
| `-julia-split-block-insts` | 8192 | per-BLOCK instruction count | SLP, ISel, early InstCombine (single huge blocks) |
| `-julia-split-block-safepoints` | 512 | per-block safepoint count | subordinate: keeps the region budget realizable from whole blocks |
| `-julia-split-region-insts` | 65536 | per-region instructions | value numbering & general linear+ work; boundary tax ~1/R wants it large |
| `-julia-split-region-safepoints` | 512 | per-region safepoints | GreedyRA / MachineCSE (rooted live ranges across calls) |
| `-julia-split-region-blocks` | 512 | per-region basic blocks | GVN's non-local memdep walk: cost ~ instructions x branchy blocks |

Outlining triggers only when a function EXCEEDS at least one full cap; a
function under every cap already satisfies every bound, so it is left whole
(this also prevents pointless whole-body extraction). A stuck region may form
once it covers >= 1/4 of any enabled cap (the "progress-fraction" floor).

## Synthetic shape generator: `gen_axes.jl`

One measurement per invocation; env vars `GEN`/`S`/`B`/`W`/`D`, prints
`gen,S,B,W,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ns_per_op,chk`.
Run with the built julia + `JULIA_LLVM_ARGS="<flags>"`, pinned (`taskset -c N`).

| GEN | shape | stresses | scaling (unsplit) |
|---|---|---|---|
| `straight` | S muladds, W dependent chains, ONE block | SLP (O(S^2)ish), ISel, MachineScheduler | 67s at S=64000 vs 1.5s split |
| `blocks` | branchy diamonds of ~B stmts, no calls | SLP + MachineCSE fn-global term; ONLY the region caps bound it (no safepoints exist, blocks are small) | 8.6s at S=128k vs 3.2s split |
| `calls` | C calls through W Ref chains (safepoint-dense) | GreedyRA (73% of compile unsplit), MachineCSE, GVN | 1.9s at S=16k vs 0.57s; region-safepoints is THE lever |
| `arrays`/`arrays_pure`/`arrays_store` | muladds with Vector loads (+ stores every 512) | SLP schedule-budget quirks, derived-pointer (AS11/13) remat at boundaries | runtime-sensitive shape; see caveats |
| `gvn` | branchy store-wall + redundant reloads GVN must forward past it (diamond every B units) | GVN's insts x branchy-blocks memdep walk, in-pipeline (julia-level analogue of mwe-gvn-storewall) | 2.3s at S=2000 unsplit |
| (D>0 for `calls`) | FP filler per call | safepoint-density dilution | |

## Observed pass scaling (measured on these MWEs; stated only where well-measured)

| pass | observed scaling | measured on |
|---|---|---|
| GVN | linear(insts) + superlinear(insts x BRANCHY blocks); raw unconditional blocks free | mwe-gvn-storewall discriminators |
| GVN (bare, branchy loads) | ~O(N^3) | 13.5s@4k -> 105s@8k, opt -passes=gvn |
| SLP | superlinear in single-block size (local exp 1.3 -> 2.3 by 32k); plus a fn-global term on many-small-block shapes | straight, blocks |
| InstCombine (isKnownNonZero/comesBefore) | O(calls x block size) = clean O(N^2) in one block | mwe-instcombine-quadratic |
| GreedyRA | superlinear in per-function rooted live ranges across safepoints (x13 at 2x size) | calls, mwe-regalloc-callblock |
| MachineCSE | superlinear on call-dense functions (x3.6 at 2x) | calls |
| X86 ISel | superlinear in block size (x3.9 at 2x) | straight |
| MachineScheduler | shape-dependent: block-scale on single-block code, fn-scale on call-dense | straight, calls |
| JuliaLICM | O(K^2) in allocs hoisted per loop (MemorySSA insertDef renames dominated subtree); cross-loop propagation adds ~O(loops^2) | mwe-julialicm-hoist |
| IRCE | superlinear on tracked ReverseDiff (collapses under any outlining); not root-caused | reversediff |

## Per-MWE notes

- `mwe-gvn-storewall/` — GVN redundant load-forwarding across a branchy
  store-dense CFG (the tracked-ReverseDiff GVN pathology under bare
  `opt -passes=gvn`). Canonical `gen.py` phis the load POINTER through each
  diamond so MemDep must PHI-translate it. Discriminators gen3/4/5 established
  the cost model: GVN = linear(insts) + superlinear(insts x BRANCHY blocks);
  raw unconditional blocks are free; block count with a fixed block count is
  linear (rules out insts^2). Motivates `-julia-split-region-blocks`.
- `mwe-instcombine-quadratic/` — InstCombine `visitCallBase -> isKnownNonZero
  -> isValidAssumeForContext -> comesBefore -> renumberInstructions`,
  O(calls x block size) in ONE huge block. Faithful in-pipeline form: operand-
  bundle nonnull assumes (`"nonnull"(ptr %p)"`), which SURVIVE EarlyCSE
  (icmp-ne-0 assumes get discharged and only reproduce under bare opt).
  Bounded by block chunking at ANY block-insts <= 8192 (flat 0.17-0.19s vs
  24.3s off at N=16000).
- `mwe-julialicm-hoist/` — JuliaLICM O(K^2): K non-escaping `julia.gc_alloc_obj`
  hoisted from one loop; each MemorySSA insertDef renames the dominated
  subtree. Must run isolated (`opt -passes='function(loop-simplify,loop-mssa(JuliaLICM))'`)
  because AllocOpt eats the allocs in-pipeline. Multi-loop variant is fixed by
  outlining (each loop its own function kills cross-loop renames); single-loop
  is a known counter-example (no cut exists).
- `mwe-regalloc-callblock/` — giant call block, cumulative live values.
  GreedyRA superlinear. KEY: block-splitting does NOT help (SSA values stay
  live across BB boundaries); only outlining (marshalling through memory)
  breaks the ranges. Why region-safepoints exists.
- `mwe-branchy-loop/` — counter-example: branchy call-dense single LOOP
  (IndVarSimplify/ConstraintElim superlinear). NEITHER lever helps — the
  splitter cannot outline a single loop body (no single-entry cut). Future
  work: multi-entry/dispatch extraction.
- `mwe-instcombine-sink/` — InstCombine sinking regroups interleaved FP chains
  at region seams; RegisterCoalescer large-interval throttle + Zen4 post-RA
  scheduler then "weld" the chains serial (5.2x runtime, MN=400 repro). The
  motivation for the two custom-LLVM InstCombine commits and/or
  mergeStraightSeams (see A/B notes in NOTES.md).
- `reversediff/` — the flagship REAL workload: tracked ReverseDiff on a
  Symbolics-generated brusselator RHS. `reversediff_mwe.jl` (`RD_N=N`, needs
  only ReverseDiff installed) compiles the pregenerated `reversediff_fexpr_N*.jl`
  kernels (N = 4..32; IR ~ 2N^2 equations) and reports compile + LLVM time;
  `reversediff_scaling.jl` is the original ModelingToolkit/Symbolics harness
  that generates the kernels and compares Float64/Dual/TrackedReal scaling. N=6 kernel: 156k lines, 13.8k blocks, 23k loads,
  33k stores. Off-split scaling ~O(size^2.15); with defaults ~O(size^1.12)
  (N=8: 62.7s -> ~12s; N=10: 163s -> 19s). Safepoint-BOUND at large targets
  (cuts 0/x/0), stuck-clamp-bound at small ones; compile-optimal region
  ~470-1400 insts, stable across N.

## Known runtime caveats

- `arrays_store` has an SLP schedule-budget toxic zone for regions ~1.5-3k
  insts (gather storms, up to +64% runtime); the 65536-inst region default
  sits safely above it. An unexplained 0.305 ns/op reading at final defaults
  (vs 0.137 under an older config) needs a block-safepoints 128-vs-512 A/B.
- Splitting is otherwise runtime-free on these shapes (+/-1-4% boundary tax,
  falling as 1/region-size).

## A/B verdict: custom-LLVM InstCombine commits vs mergeStraightSeams (item 3)

Runtime ns/op at final defaults, {fixed = with the two InstCombine commits,
stock = without} x {seam-merge on/off}:

| lib | merge | straight-65536 | arrays_store-64000 | blocks-128000 |
|---|---|---|---|---|
| fixed | on  | 0.135 | 0.305 | 0.165 |
| fixed | off | 0.135 | 0.305 | 0.165 |
| stock | on  | 0.218 (+61%) | 0.405 (+33%) | 0.165 |
| stock | off | 0.275 (+104%) | 0.475 (+56%) | 0.165 |

**Verdict: KEEP BOTH.** Stock LLVM regresses REPRESENTATIVE straight-line FP
shapes, not just the synthetic weld MWE: mergeStraightSeams helps stock but is
insufficient because its cap (4 x block-insts = 32768) is below region-insts
(65536), so region bodies retain mid-body seams that stock InstCombine sinks
chains across (-> coalescer/post-RA welding). With the fixed LLVM, merge
on/off are identical — the InstCombine fix fully protects runtime; the merge
is retained for block-local analysis scope. The custom-LLVM dependency stays
until the two commits are upstreamed (llvm-project branch
instcombine-sink-colder-blocks: equal-frequency sink guard + order-preserving
sink sweep).
