# SOLVED: split straight-line code now converges to unsplit

Resolution of the failed-asymptote handoff (this file's previous contents).
Root-caused and fixed on the Zen 4 box (EPYC 9354), 2026-07-03. The fix is
committed alongside this note in `src/llvm-function-splitting.cpp`
(`mergeStraightSeams` + caller-side call-block merge in `processLevel`).

## Root cause: InstCombine's single-use code sinking

Not our transform, not the backend, and (as suspected) not a boundary cost.
InstCombine canonicalization `TryToSinkInstruction`: an instruction with
exactly one use in a DIFFERENT block is moved to that block's FIRST insertion
point, and its operands go back on the worklist. Across the unconditional
seams the splitting pass leaves behind, that cascades: sinking a chain's tail
makes its producer single-use-cross-block too, so the entire dependency chain
relocates one instruction at a time, each landing above the previously sunk
one. Result: interleaved independent chains come out CHAIN-GROUPED (the
observed runs of 1240-1600 consecutive vfmadd on one accumulator), i.e. one
serial 4-cycle latency chain at a time. Run length = chunk/8 per chain, so
the damage GROWS with region size: the anti-asymptote.

Two seams trigger it; one shape is immune:

- parent: chunkA -> [codeRepl: call @region] — chain tails are call args in
  the next block => ALL of chunkA sinks into the call block, grouped.
- region: chunkB -> chunkC inside a multi-chunk region body — same cascade.
- immune: the LAST chunk of each function (parent reduction tree, region
  output stores placed at defs) consumes chain ends IN-BLOCK: no single-use
  value crosses, nothing sinks. This was the handoff's untested
  "spill stores vs reduction tree" hypothesis — right structural cue.

## Evidence chain (all on Zen 4; machine-independent mechanism)

1. Repro: straight S=65536, SLP off — off 0.135, c1600 0.139, c6400 0.136,
   c12800 0.168, c25600 0.200, c51200 0.270 ns/op (tiny variance). Same
   phenomenon as ADL, knee shifted right (bigger OOO window).
2. Machine code (parent_bytes.jl + objdump): ~7800 of ~10900 parent FMAs in
   serial runs of 1242-1420 on %xmm1. Same smoking gun as ADL.
3. IR dataflow distance test (asymptote/chain_dist.py, d0=grouped,
   d7=interleaved): final IR already grouped => IR-level producer.
4. -print-after bisect (chain_dist_seq.py over
   -print-after=JuliaFunctionSplitting,instcombine,... -filter-print-funcs):
   IR is 100% d7 immediately after FunctionSplittingPass; the FIRST
   InstCombine after it (pipeline.cpp GlobalFPM) flips half the links to d0.
   Block accounting is unambiguous: parent entry 25,602 insts -> 9; the
   2-inst call block -> 25,594, chain-grouped.
5. Decisive control: -instcombine-code-sinking=false => EVERY chunk size runs
   exactly 0.135 = unsplit.

## The fix

At the end of processLevel, after all nested extraction (so no child
Region::Blocks pointer is used after a merge erases a block):

- mergeStraightSeams(NewF, Cap): MergeBlockIntoPredecessor for every block
  with unique pred / single-successor pred (SimplifyCFG's own merge rule —
  cannot fuse real control flow), capped at 4*SplitChunkSize (mirrors
  growRegion MaxSize) so hierarchical-parent glue can't fuse unboundedly.
- caller side: each region's codeRepl block folds into its unique
  predecessor, so call operands stay in the same block as their defs.
  Residual chunk-chunk seams in the caller are KEPT (block-size bound);
  only output reloads cross them, and loads have no chains to cascade.

## Validation (Zen 4, straight S=65536, SLP off, stock InstCombine)

    chunk    off    c400   c1600  c6400  c12800 c25600 c51200
    before   0.135  0.151  0.139  0.136  0.168  0.200  0.270
    after    0.135  0.148  0.138  0.136  0.135  0.135  0.135

Monotone convergence to the exact unsplit value; final IR 100% d7 in both
parent and region. No regressions: calls on/off 9.61/9.57 ns/op; blocks
forced-on ratio matches the historical pre-fix sweep (the known c400 tax);
function-splitting.ll lit test passes; llvmpasses suite otherwise green
(pipeline-o2.jl fails from an unrelated /tmp/.julia permission collision on
the shared box); clang-sa/clang-tidy/clang-sagc clean.

## For the ADL/WSL session

- Re-run the original divergence table (this file's git history has the
  commands); expect flat 0.16-0.18 at every chunk size now.
- Prior small-chunk "boundary tax" numbers on chain-heavy shapes include a
  sinking component (here c400 only dropped 0.151->0.148, but ADL diverged
  from c1600 already — its tax numbers may shift more). Worth re-running
  any sizing sweep whose conclusions leaned on straight/chain workloads.
- Verify tooling: asymptote/chain_dist.py (final-module d0/d7 histogram) and
  asymptote/chain_dist_seq.py (same test over -print-after dump streams).

## Known residual exposure (deliberately not covered)

- Adjacent UNEXTRACTED chunks in the parent (growRegion-failure paths) still
  have sinkable seams; a chain crossing several retained seams drains through
  all of them, so a size-capped merge would NOT contain it — if this ever
  matters, break the single-use property at the seam (store at def, like the
  region output path) instead of partial merging.
- The Regions.empty() early return (blocks chunked, nothing extracted)
  leaves all chunk seams in place.
