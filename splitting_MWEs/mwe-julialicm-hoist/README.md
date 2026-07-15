# MWE: JuliaLICM O(K²) hoisting many GC allocations from one loop

Standalone repro of a super-linear scaling in `JuliaLICMPass` (the Julia
loop-invariant-code-motion pass) that is distinct from every other MWE in this
collection: the cost is in the **MemorySSA updater**, driven by the number of
allocations hoisted out of a single loop.

## Mechanism (perf-grounded, single loop so it can't be the verifier)

JuliaLICM hoists loop-invariant, non-escaping `julia.gc_alloc_obj` calls to the
loop preheader. Each hoist is a `moveInstructionBefore(..., MSSAU)` that inserts
a `MemoryDef` in the preheader; the MemorySSA updater then re-runs
`MemorySSA::renameBlock` over the preheader, which is O(#memory-defs in that
block). Doing this for K allocs — the preheader accumulating one more def each
time — is **O(K²)**.

`perf` on isolated JuliaLICM (K=3200):

    45.6%  llvm::MemorySSA::renameBlock            <- the quadratic
     0.3%  jl_alloc::runEscapeAnalysis             <- NOT the cost

So escape analysis (the natural suspect) is negligible; the pathology is the
per-hoist MemorySSA rename.

## Measured (isolated JuliaLICM)

    K:        400     800    1600    3200
    time:   0.026   0.098   0.410   1.610  s      (~4x per 2x K = O(K²))

M (field-ops per alloc) is only ~linear (K=800: M=4/8/16/32 → 0.063/0.108/
0.164/0.295 s) — confirming K (the hoist count) is the quadratic variable.

## Reproduce

    python3 gen.py 3200 8 > q.ll
    opt --load-pass-plugin=libjulia-codegen%shlibext \
        --passes='function(loop-simplify,loop-mssa(JuliaLICM))' \
        -time-passes q.ll -o /dev/null        # look at the JuliaLICMPass line

**Must run JuliaLICM in isolation.** In the full Julia pipeline, `AllocOpt`
runs before JuliaLICM and promotes these non-escaping allocations away, so they
never reach the loop pass. This MWE therefore exercises the pass's intrinsic
scaling, not an end-to-end compile-time regression.

## Why the ingredients are load-bearing

1. **`julia.gc_alloc_obj` (or `write_barrier`/`gc_preserve_begin`)** — JuliaLICM
   early-exits (`llvm-julia-licm.cpp:157`) if the module declares none of them,
   so plain LLVM allocas never trigger it.
2. **Loop-invariant args** (`%pg`, `%ty`, constant size) — required for the
   alloc to be a hoist candidate.
3. **Non-escaping** — the object pointer is only stored *into* (never stored
   elsewhere / returned / passed to an unknown call), so escape analysis clears
   it for hoisting and the move (and its MSSA update) actually happens.
4. **Kept live** — field 0 is read back into the returned accumulator, or DCE
   deletes the alloc before LICM.

## Relationship to the ReverseDiff investigation

This is NOT the mechanism behind the ReverseDiff megafunction's apparent
"JuliaLICM 12s". That was a `JL_VERIFY_PASSES` assertions-build artifact:
`verifyLLVMIR(const Loop&)` (`pipeline.cpp:1187`) verifies the *whole parent
function*, and JuliaLICM runs it after every loop, so 224 loops × O(funcsize)
looked super-linear (causally: 15.1s → 0.0016s with the per-loop verify
disabled). Real JuliaLICM on that function is linear. The genuine ReverseDiff
release-build bottleneck is GVN + IRCE. This MWE is a separate, real quadratic
that happens to live in the same pass.

## Levers (shape-dependent — this is the `branchy-loop` apply-failure, NOT an
## intrinsic limit of splitting on JuliaLICM)

The quadratic has two components: a **per-loop** part (each hoist re-renames the
one preheader, growing O(K)) and a **function-global** part (inserting a def in
an early loop's preheader makes `renameBlock` propagate across every dominated
downstream loop). The second part is why K allocs spread over m loops does NOT
drop to (1/m)·cost:

    K=3200 total, over m loops (isolated JuliaLICM):
    m=1        m=2        m=4        m=8
    1.56s      1.18s      0.93s      0.91s     (floor if purely per-loop: ~0.21s)

Measured lever effects (isolated JuliaLICM):

    shape                off     block-split     function-split
    single loop K=3200   1.65s   2.13s (worse)   2.19s (worse, 2 fns)
    multi-loop 8x400     0.91s   1.14s (worse)   0.21s (4.4x, 9 fns)

- **Single loop (this MWE as written)**: splitting has NO applicable cut — it
  cannot subdivide one loop. Function-split wholesale-outlines the loop into a
  region function (+ shim) and adds marshalling → slightly worse. Block-split
  just adds blocks/memory-phis to rename → worse. Same failure mode as
  `mwe-branchy-loop`.
- **Multi-loop (the realistic ReverseDiff shape — 224 loops)**: **function-split
  DOES help** — it outlines each loop into its own function, so a hoist's
  `renameBlock` can no longer propagate to other loops. That kills the
  function-global component and hits the per-loop floor (0.91s → 0.21s).
  Block-split still doesn't help: it doesn't outline, so all loops stay in one
  function and the cross-loop propagation remains.

So splitting is not powerless against this JuliaLICM quadratic in general —
function-split bounds it whenever there are multiple loops to separate. It fails
only on the single-loop shape, where no cut exists.

## Mitigation via function-splitting (the chosen approach)

The in-pass fix was abandoned (see below); the practical mitigation is the
function-splitting pass, which already runs before the loop optimizer in the
Julia pipeline (`SplitBuiltinLate`, pipeline.cpp:692, ahead of
`buildLoopOptimizerPipeline`). It LINEARIZES the loop-count scaling by outlining
each loop into its own function (fixed 200 allocs/loop, scaling loop count m):

    m (loops)  total allocs   noSplit    fnSplit
    4          800            0.064s     0.026s
    8          1600           0.241s     0.052s
    16         3200           0.932s     0.101s
    32         6400           3.565s     0.203s   (17.6x; gap widens with scale)

noSplit is ~O(m^1.9); fnSplit is exactly linear (2x per 2x m). Robust to
region-size (800/3200/6400/20000 all outline each loop → ~0.21s at m=32).
**Function-split only** — block-split does NOT help (3.79s at m=32; it doesn't
outline, so the dominated subtree each renameBlock walks is unchanged). This is
the same universal function-split lever that bounds GVN/RA/CSE, and it needs
splitting enabled with a nonzero `-julia-split-function-threshold` (off by
default). Only the single-loop shape is left unmitigated (no cut).

## Why the in-pass fix was abandoned

`insertDef(MemoryDef, RenameUses=true)` runs `renamePass` over the whole
dominated subtree, once per def placed in the preheader → K·O(subtree) = O(K²).
BOTH the memset insert AND the alloc *move* pay it: `moveToPlace` for a
MemoryDef routes through `moveTo` → `insertDef(RenameUses=true)`
(MemorySSAUpdater.cpp:1170), so "move the existing def like upstream LICM" is
not cheaper — a MemoryDef move IS an insertDef. A targeted memset re-point
(shadow the alloc, O(uses)) is cheap and structurally valid but only removes the
memset half (still O(K²) from the alloc move). LLVM has no bulk insert-defs API.
The only correct in-pass fixes are (A) batch hoists + one MemorySSA recompute,
or (B) an upstream bulk `insertDefs`; both need an EXPENSIVE_CHECKS LLVM build to
validate clobber-semantic correctness (the assertions-build MemorySSA verifier
is structural-only). Since the quadratic only bites when many hoistable allocs
survive to JuliaLICM in one function (rare — AllocOpt usually removes them),
function-splitting is the pragmatic mitigation.
