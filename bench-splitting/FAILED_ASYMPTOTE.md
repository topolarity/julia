# FAILED ASYMPTOTE: split straight-line code never converges to unsplit

Handoff for the Zen/PMU machine. Helper scripts in `asymptote/` (run from
`bench-splitting/`; they include their own generator, no envs needed).

## The phenomenon (so far only measured on the ADL/WSL box)

Shape: `straight` (GEN=straight, one giant FMA block over 8 round-robin
chains), SLP DISABLED everywhere. As regions grow, split runtime should
converge to unsplit; instead it diverges monotonically AWAY from it
(ns per executed op, S=65536):

    off    c400   c1600  c3200  c6400  c12800 c25600 c51200
    0.16-0.18  0.16-0.20  0.23   0.32   0.41-0.45  0.56   0.54   0.56-0.61

At c51200 there is ONE region + residual (a single boundary): 3.5x slowdown
from one boundary is impossible, so this is NOT a boundary cost. The blocks
(branchy) shape converges normally on both machines — this is specific to
branch-free chain code.

## Eliminated (do not re-chase)

- Boundary marshalling: one boundary at c51200; excess is ~25us.
- Code bloat: post-opt module insts identical (off 131,777 / c6400 132,404 /
  c51200 131,810; STATS=1 in gen_axes.jl).
- Block size per se: UNSPLIT functions of S=1600..65536 (single block, no
  pass) improve monotonically 0.30 -> 0.175 ns/op. No hump.
- MachineScheduler: -enable-misched=false -> bit-identical runtimes
  (compile time changed, so the flag was live).
- SelectionDAG scheduler: -pre-RA-sched=source -> bit-identical.
- Constant pool: dumped region rodata is the expected 128B, deduplicated.

## The smoking gun

Runtime machine-code dump of the residual parent at c51200 (F retains
~14k FMAs + 1 region call; see `asymptote/parent_bytes.jl`, then
`objdump -D -b binary -m i386:x86-64`): the FMAs are CHAIN-GROUPED —
runs of 1420-1600 consecutive `vfmadd213sd` on a SINGLE accumulator
(pattern: 6 x [1420 xmm1 + 179 xmmK], then 1599 xmm1 + 1600 xmm0; addends
are the 7 in-register constants rotating, multiplier in xmm15). The source
order interleaves 8 independent chains per 8 instructions. Grouped order =
one 4-cycle dependency chain at a time, OOO window can only overlap run
tails => latency serialization; magnitude matches the slowdown.

Critically: a same-size UNSPLIT function does not exhibit this (u6400 runs
fine), so the grouping afflicts pass-produced functions specifically.
Untested hypothesis for the trigger: region bodies END in 8 independent
spill stores (our aggregate output marshalling), unsplit ends in an 8-way
reduction tree — different DAG roots may steer whatever does the grouping.
Since both backend schedulers are nulled by flags, either (a) some other
codegen component orders it, or (b) the FINAL LLVM IR is already grouped.

## Next steps (in order)

1. Reproduce on Zen: from bench-splitting/,
   `FL="-vectorize-slp=false -julia-split-function-threshold=64
   -julia-split-block-threshold=64 -julia-split-max-region-blocks=8192"`
   then GEN=straight S=65536 with JULIA_LLVM_ARGS="$FL
   -julia-split-chunk-size=..." for off/c400/c6400/c51200 via gen_axes.jl.
   Watch the ns_per_op column. (If it does NOT reproduce on Zen, that is
   itself decisive: uarch-specific like the SLP-width effect — then just
   PMU the ADL... i.e. report and stop.)
2. Confirm grouping: `asymptote/parent_bytes.jl` (region address extraction
   via CodeInstance.specptr + movabs scan; parent = residual F) and the
   accumulator run-length awk from NOTES history:
   `grep -oE 'vfmadd213sd xmm[0-9]+' | uniq -c`-style.
3. Decide IR vs backend: `asymptote/ir_order.jl` dumps the final module IR
   (code_llvm raw dump_module optimize=true). NOTE: muladd is fmul+fadd
   with `contract` flags in optimized IR, NOT llvm.fmuladd — test chain
   grouping via dataflow distance between consecutive `fadd contract`
   results (interleaved: producer ~8 instructions back; grouped: previous
   instruction). The first parse attempt matched on "fmuladd" and found 0.
4. If the final IR is grouped, bisect the producer pass:
   `JULIA_LLVM_ARGS="$FL -julia-split-chunk-size=6400 -print-after-all
   -filter-print-funcs=julia_bench_f_0"` (filter makes the volume sane),
   apply the distance test to each snapshot, find the first grouped one.
   Suspects worth pre-checking: anything with reassociation semantics
   (fadd here carries only `contract`, which should NOT license
   reordering), and our own pass's insertion order around the spill
   stores.
5. If the final IR is NOT grouped: the producer is in ISel/regalloc despite
   the two null flags. Controls: verify the flags change ANYTHING
   (-pre-RA-sched=list-burr vs source should at least perturb); then
   llc-replay the dumped IR with -print-after-all at the MI level.
6. PMU sanity along the way: the serialization signature is low IPC with
   NO elevated fills/mispredicts (pure dependency stalls, backend-bound,
   long fp_ret latency) — cheap to confirm the mechanism class before
   bisecting.

## Why it matters / scope

With SLP ON this shape is flat across region sizes (packing hides it), and
the branchy shape is unaffected — so current sizing conclusions stand. But
non-vectorizable chain code (mixed-latency scalar math) is a real workload
class, and if some pass/backend component serializes chains in extracted
functions, that is a genuine transform-induced pessimization with no
structural limit — the one place where "split code = unsplit code + small
tax" is currently false.
