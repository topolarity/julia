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
- The backend pipeline is order-preserving in both directions at this
  scale: the pre-RA scheduler neither fixes grouped input nor destroys
  interleaved input. What decides the outcome is register allocation's
  response to the input order under pressure. Grouped input + low
  pressure: each chain's live range gets its own register, and the
  post-RA scheduler then interleaves freely (the observed "rescue").
  Grouped input + high pressure (the coefficients are live across the
  call; x86-64 has no callee-saved XMM): RA assigns every chain's run to
  the SAME register with spills between runs — locally optimal for the
  grouped order — and the resulting physical anti-dependencies and
  spill-slot memory deps hard-block any later reordering. Interleaved
  input under the same pressure runs at full speed (RA folds the cheap
  read-only spills), proving the pressure only blocks the CONVERSION of
  grouped to interleaved, not interleaved execution itself. Exceeding
  the register file alone does not reproduce the problem (verified with
  12- and 18-accumulator variants): the grouped order is the essential
  co-ingredient.
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
