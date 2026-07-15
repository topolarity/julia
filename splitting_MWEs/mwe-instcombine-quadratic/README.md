# MWE: InstCombine O(calls x block-size) — the tracked-ReverseDiff quadratic

Reproduces the compile-time quadratic documented in NOTES.md
("calls in huge blocks | InstCombine isKnownNonZero -> renumberInstructions
O(calls x blocksize)"), originally hit by the tracked ReverseDiff workload
(N=48: 425s -> 98s with splitting).

**IN-PIPELINE faithful (2026-07-06 rewrite).** The path is
`visitCallBase -> isKnownNonZero(pointer arg) -> isValidAssumeForContext ->
comesBefore -> renumberInstructions`, and the nonzero fact comes from a
`nonnull` OPERAND-BUNDLE assume — `llvm.assume(i1 true) ["nonnull"(ptr %p)]` —
which is the form Julia emits for tracked pointers. That form **survives
EarlyCSE/InstSimplify**, so the quadratic reproduces in the *full pipeline*, not
just bare `opt`:

    N=8000:  bare instcombine 6.2s | julia pipeline (off) 6.1s | split#1(bb<=2000) 0.086s  (~75x)

The PREVIOUS version of this MWE used an `icmp ne %d, 0`-conditioned assume
guarding a `udiv`. That reproduces O(N^2) in bare `opt -passes=instcombine`, but
EarlyCSE discharges the icmp-conditioned assume (marks the icmp true) *before
any InstCombine*, so it was **linear in-pipeline** (~0.35s) and never exercised
split#1 — a misleading bare-only reproducer. The bundle form above is the one
that matches reversediff and demonstrates split#1's fix.

## Mechanism (confirmed against LLVM 21 source)

InstCombine visits an instruction whose fold consults `isKnownNonZero` on a
value that is only provably nonzero via a same-block `llvm.assume`. ValueTracking
calls `isValidAssumeForContext`, which calls `Instruction::comesBefore` to check
the assume precedes the use. `comesBefore` re-runs `BasicBlock::renumberInstructions`
(O(block-size)) whenever the block's instruction-ordering cache is stale — and it
is stale after any insertion/removal in the block. So the two necessary
ingredients are:

1. many such guarded queries (here: `udiv` by an assume-guarded divisor), and
2. interleaved instructions InstCombine rewrites (`add %p,%p` -> `shl`), which
   invalidate the ordering cache before each query.

Without (2) the cache stays valid, `comesBefore` is O(1), and the whole pass is
linear (this is why a naive assume+udiv block does NOT reproduce it).

Total cost is O(N * block-size) = O(N^2).

## Reproduce (opt only, deterministic)

    python3 gen.py 4000 0  > huge.ll   # one block
    python3 gen.py 4000 64 > split.ll  # chunked to 64-op blocks
    opt -passes=instcombine -time-passes huge.ll  -o /dev/null   # quadratic
    opt -passes=instcombine -time-passes split.ll -o /dev/null   # linear

Measured (opt from this build, InstCombine wall):

    N       huge-block   split-64
    2000    0.228s       0.037s
    4000    0.841s       0.074s      (~4x per 2x N = O(N^2) vs ~2x = linear)

Fixed by CHUNKING the block (Julia's BasicBlockSplitting / the pre-InstCombine
split position). Independent of the equal-frequency sink gate: opt-prefix
(stock) and opt-fixed give the same time (0.833 vs 0.844s at N=4000), i.e. the
sink fix neither causes nor hides this.

## In the wild (tracked ReverseDiff)

The tracked ReverseDiff brusselator RHS reproduces the same super-linear compile
(splitting off): N=6 (n=72) 100s, N=8 (n=128) 323s, N=10 did not finish in 10min.
NOTE: confirming the in-workload split *fix* is currently blocked by a separate
bug — FunctionSplitting produces invalid IR on this shape (a GC-frame alloca
fails to dominate its uses; verifyFunction assert at llvm-function-splitting.cpp).
See followups.
