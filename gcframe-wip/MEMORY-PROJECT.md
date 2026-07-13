# Exported project memories (gcframe/lifetime campaign)

Exported 2026-07-11 for machine migration. These are point-in-time notes; verify
file:line citations against current code.

## jl-stack-usage-diagnosis

Diagnosed 2026-07-10. JuliaLowering recursive tree-walkers have 5–12KB frames
(est_to_dst 12,096; vst1 11,712; expand_forms_2 9,760; vst2 7,872; compile 5,760).
Survey: 2,160 JIT specializations (`stack_survey.jl` used a probe-aware `sub rsp`
parser — prologues use 4096-byte stack probes, naive parsing truncates).

expand_forms_2 anatomy (9,704B locals ≈ 9,424B from 405 entry-block allocas, i.e. zero
slot merging):
- 2,416B = 151× 16B `sret::SyntaxTree`, one per call site returning SyntaxTree
- 2,704B = 169× UnitRange temps, ALL feeding `j__throw_boundserror` (cold error paths);
  `--check-bounds=no` shrinks frame 35%
- 2,176B gcframe [272 x ptr]: ~160 slots were per-call-site return_roots appended
  UNCOLORED (`S.ArrayAllocas` loop skips ColorRoots); ~110 "colored" slots later shown
  to be mostly argument-staging buffers, true colored region ~19 and healthy
- rest: SubArray views, closure envs, SyntaxList temps

Root causes: (1) Julia codegen emits one alloca per call-site temp with NO lifetime
intrinsics (TODOs at cgutils.cpp:4214, codegen.cpp:6142) → LLVM StackColoring can't
merge mutually-exclusive branches of the giant kind-switch; (2) return_roots slots not
liveness-colored; (3) SyntaxTree returns cost sret+return_roots slots per call site.

Whole-pipeline: lowering base/range.jl (depth-15 AST) uses ~260KiB stack (~16KiB per
AST level; Task-stack bisection method in `stack_highwater.jl`).

## jl-stack-lifetime-markers (implementation state)

Starts-only lifetime markers: `CreateLifetimeStart` at 4 codegen sites
(value_to_pointer, split_value, sret buffers, emit_new_struct — the latter guarded
against promotion: skip if `is_promotable` or any arg has a promotion point, since
promotion RAUWs the alloca and breaks marker dominance). No lifetime.end anywhere.

Why no ends: once a temp backs a `jl_cgval_t`, reads are deferred arbitrarily
(emit_getfield_knownidx returns interior pointers WITHOUT loading, even primitive
fields when parent has inline roots) — Julia-IR last-use does not bound last memory
access; only function exit does (return conv copies into caller's sret/return_roots =
the cross-frame relay). Sound ends need cgval borrow-tracking (backing-AllocaInst field
propagated through mark_julia_slot reuse; phi-edge copies are materialization
boundaries that stop borrows). Full end-machinery was archived as
`lifetime_full_machinery.patch` in the old machine's session scratchpad (NOT
transferred; reconstructible from the conversation).

Committed on ct/codegen-lifetime-starts (per-change deltas):
1. 2aefad27f6 lifetime.start: ef2 frame 9,760→5,280 (vst1 11,712→5,648; est_to_dst
   12,096→7,856; base/range.jl pipeline high-water 260→196 KiB)
2. 3f784c5a98 PackReturnRootsBuffers: ef2 frame 5,280→4,192 (−21%), gcframe 272→141
   (124 of 160 call sites share ONE slot); est_to_dst gcframe 345→217. Per-buffer
   backward liveness (uses of buffer + paired sret generate, defining calls kill),
   contiguous multi-slot first-fit packing; bails on unclassifiable users /
   returns_twice / phi-merged bases.
3. f7ccc056b6 Makefile header deps (see stale-objects note below)
4. b1a8fe0456 (A) jl_gc_roots_t::get_ptr forwards roots loaded from consecutive slots
   of readonly Argument buffers (or single invariant global loads) instead of copying —
   the dominant recursive-traversal pattern; (B') julia.gc_roots_begin intrinsic
   (argmem: write, so stores can't hoist above it) marks staging-buffer fill points →
   late-gc packs them with the return_roots machinery; FinalLowerGC backstop-erases
   leftovers. Deltas: ef2 gcframe 141→110 (fwd) →106 (pack), frame 4192→3936; after
   the Events liveness fix (annotation def-calls must enter the Events list as kills,
   else ranges smear to entry and everything interferes): gcframe →28, frame 3,312.
5. 490cae6a48 WIP (see STATUS.md): refinements 28→27, elision 27→20 (UNVALIDATED,
   open crash investigation).

Key pass facts learned:
- LLVM StackColoring (LifetimeStartOnFirstUse default on): merge test =
  interference-at-start (`!First->isLiveAtIndexes(SecondS)`), sound via the clobber
  invariant (start clobbers; every read reached from own start; policed by
  "Conservative slots"). Starts-only works because a slot with no end simply never
  closes its region; merging still happens via start-anchored interference.
- ColorRoots is PEO-greedy and exact for chordal SSA interference graphs; safepoint
  co-liveness is EXACT for SSA-with-lifted-phis (see design note below).
- Litmus (real function, arm duplication in expand_forms_2 via
  `SCALE_GUARD[n]::Bool` standalone conditions — duplicated arms must NOT be
  GVN-provably dead): parent (pre-optimization) gcframe 272/529/1,043 slots at
  M=1/2/4 vs optimized 28/39/47 — ~40× slope reduction. Residual growth suspects:
  per-arm promotable news unmarked, [min,max] interval merging in the packer.

## stack-memory-ssa-note (design)

Two interference regimes for stack storage:
- **SSA regime** (ColorRoots' colored root slots): SSA form + phi edge-stores install a
  full-clobber definition at every merge point, so path-exclusive values never share a
  name past a join. Point-based co-liveness (sampled at safepoints, with per-range
  re-stores) is then EXACT. A live-at-def refinement can only add edges there
  (safepoint-interference ⊆ live-range-overlap ≡ live-at-def under SSA dominance).
- **Memory regime** (machine stack slots / roots buffers): occupants can be read at
  merge points without a mediating definition (phi'd pointers), so point co-liveness
  over-approximates. StackColoring's start-anchored test + clobber invariant exploits
  path-exclusivity that point-sampling cannot see.

Saved idea (explicitly deferred, trade-off open): an SSA-like transformation for stack
memory — split/copy allocas at phi-join points (fresh slot + copy per incoming edge,
like phi lifting). Moves memory slots into the SSA regime where exact criteria apply;
costs runtime copies vs teaching passes live-at-def reasoning directly.
B3 chore: assert/comment the ColorRoots SSA-with-lifted-phis invariant.

## header-change-stale-objects (build trap — bitten 3× in one session)

src/Makefile lists header deps per-object explicitly (~line 495); variant objects were
missing (llvm-final-gc-lowering-stock/-mmtk — dep rules added in f7ccc056b6, but other
gaps may remain). Any struct-layout change in a shared header (llvm-pass-helpers.h,
llvm-gc-interface-passes.h, jitlayers.h...) can silently ABI-skew whichever objects
aren't listed — pipeline.o and jitlayers.o CONSTRUCT the pass objects whose methods
live elsewhere, so a struct-size mismatch corrupts the stack and presents as unrelated
LLVM assertions ("Calling a function with bad signature") or JIT hangs. If a rebuild
produces impossible-looking crashes in code you didn't touch, suspect stale objects
FIRST. The only reliable recipe after ANY header edit/revert in src/:
`make -C src clean && make -j` (~4 min; cheaper than a mis-debugging hour).

Related trap: mixed builds (new src/ runtime + sysimage/pkgimages compiled by an older
codegen, or vice versa) are an unsupported ABI mix once calling-convention/rooting
behavior changes — resolve by full bootstrap (rm images + make) before debugging
"impossible" crashes.

## jl-invalidation-root-causes (context for why JuliaLowering recompiles at load)

Loading packages invalidates Base methods: only `cconvert`/`&`/`|` kill JuliaLowering
(≤3-method widened edges); `==`, `+`, `convert`, `Symbol` are immune (>4 matches).
Relevant here because `--compiled-modules=no` runs trigger in-process recompilation of
Base/parser methods with the WIP pass — that's how a pass bug corrupts `fl_lower`-era
code paths during JuliaSyntax load (see STATUS.md crash investigation).

## Deferred follow-up (user-approved)

Const-field TBAA: best_field_tbaa (cgutils.cpp:3418, has a TODO) only gives
`tbaa_const` to const fields when the parent is a const-GV load; const fields of heap
objects (e.g. SyntaxGraph.edges) keep mutable TBAA → no CSE across calls (5-6 duplicate
.edges loads per walker). Proper fix is an aliasing-soundness design (loads must not
float above constructing stores; cf. invariant.group). Independent of the gcframe
campaign; take up only after the overall project is done.
