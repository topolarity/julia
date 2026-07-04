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
- The backend CAN usually rescue grouped chains by rescheduling — unless
  interleaving is blocked by register pressure at the call: the reused
  coefficients are live across the call (x86-64 has no callee-saved XMM),
  so interleaving would need 8 accumulators + 8 live-across values > 16
  XMM registers, and the pressure-aware scheduler keeps the grouped order.
  (Without ingredient 3 the constants die at the call and llc rescues the
  grouping completely; without ingredient 2 likewise.)

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
