# Standalone repro: InstCombine equal-frequency sinking pessimization

Minimal demonstration for the LLVM patch
"[InstCombine] Do not sink instructions across equal-frequency edges"
(~/repos/llvm-project branch instcombine-sink-colder-blocks).

## The kernel (gen_kernel.py, ~40 lines)

8-lane batched polynomial-chain evaluation (the multi-accumulator /
Estrin-style ILP pattern), written interleaved as any performance-aware
source is, with three structural features:

1. a straight seam (`br label %stage2call`) before the combining call —
   as left by block-partitioning passes (e.g. Julia's function splitter);
2. a call consuming the 8 chain results (a pipeline stage boundary);
3. a short continuation after the call reusing the same coefficients.

## The mechanism (each ingredient necessary, verified by ablation)

- Stock InstCombine sinks the single-use chains across the seam one
  instruction at a time; the cascade reassembles all 8 chains contiguously
  (runs of ~1600 dependent FMAs).
- The decision point is register allocation, not scheduling (verified in
  MIR): after the pre-RA machine scheduler, welded and rescued cases look
  the SAME — still grouped, partially chunked into ~355-op runs per
  virtual register (each chain is one coalesced, re-defined vreg by then).
  The lock is REGISTER RE-USAGE installed by RA: in the failing case all
  chain runs are assigned the same physical register (%xmm1) with spills
  between runs, and the resulting anti/output dependencies plus
  spill-slot memory deps freeze the order for the post-RA scheduler and
  everything after. In the rescued case RA hands the chains distinct
  registers and the post-RA scheduler interleaves freely.
- What drives RA to share vs spread is the register squeeze from HOT
  live values: the reused coefficients are touched every step on both
  sides of the call (and cannot be folded once MachineCSE keeps them in
  registers), pinning ~8 registers. IDLE pressure does not do this:
  18 accumulator chains with no hot extras (sink verified grouped,
  18 runs of 1600) are fully rescued — waiting accumulators cost one
  spill/reload per entire run and leave head-room. Exceeding the register
  file alone therefore does NOT reproduce the problem; grouped order x
  hot cross-boundary values is the necessary pair.
- Open puzzle for the upstream report: RA welds within xmm0-15 and never
  touches xmm16-31 even though the ops are EVEX-class (fr64x, 32
  registers available) — the sharing is a heuristic choice (allocation
  order / encoding cost), not exhaustion of the architectural file.
  Register-level signature: failing build has all runs on %xmm1;
  rescued build has 8 distinct accumulator registers.

## Reproduce

    python3 gen_kernel.py                     # MN=1600 SCRATCH=. -> mwe_final.ll
    opt-stock   -passes=instcombine mwe_final.ll -S -o stock.ll
    opt-patched -passes=instcombine mwe_final.ll -S -o patched.ll
    llc -O2 -mcpu=znver4 {stock,patched}.ll ; gcc -O2 driver.c ...

## Measured (Zen 4 / EPYC 9354, LLVM 21.1.8 base)

    stock   InstCombine: 10433 ns/call   0.816 ns/step
    patched InstCombine:  1702 ns/call   0.133 ns/step   (6.1x)

Onset vs chain length N (grouped-vs-interleaved, direct generation):
N=200 no delta (OOO absorbs); N=400 1.8x; N=800 1.9x; N=1600 6.1x.

Identical output sums in all configurations.
