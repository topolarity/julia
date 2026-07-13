# GC-frame minimization campaign — WIP status (2026-07-11)

Branch `ct/codegen-lifetime-starts`. Committed so far:
- `2aefad27f6` codegen: llvm.lifetime.start for private stack temporaries (ef2 frame 9760→5280)
- `3f784c5a98` gc: PackReturnRootsBuffers — share GC frame slots between disjoint return_roots buffers (→4192, gcframe 272→141)
- `f7ccc056b6` Makefile header deps (llvm-final-gc-lowering-stock/-mmtk on llvm-gc-interface-passes.h)
- `b1a8fe0456` roots forwarding in jl_gc_roots_t::get_ptr + julia.gc_roots_begin intrinsic + 2b fixes
  (gcframe 141→28 after the Events liveness fix; ef2 frame 3312)

## This WIP commit (uncommitted work, needs cleanup before merging)

`src/cgutils.cpp`:
- `julia.constant_field` metadata on const-field pointer loads in emit_getfield_knownidx
  (aliasing-neutral; consumed only for root refinement).

`src/llvm-late-gc-lowering.cpp` (contains TEMP DEBUG code — JL_REFINE_DUMP, JL_SLOT_MAP
prints, JL_ELIDE_MAX gate, JL_ELIDE_POISON knob — strip before merge):
1. Refinement (2): consume `julia.constant_field` in LoadInst branch; new
   `isLoadFromCallerRoots()` → refine loads from readonly ptr-arg roots buffers to -1
   (both LoadInst and AddrSpaceCastInst branches). Measured: gcframe 28→27 alone.
2. `terminally_rooted` skip of TrackedStores shadow slots (all-negative refinement ⇒ no
   shadow slot). Eliminated all shadow slots on expand_forms_2.
3. NEW (under JL_ELIDE_MAX gate, default OFF): "alloca elision" —
   `contents_terminally_rooted(AI)`: an ArrayAlloca whose every tracked store is
   terminally rooted, address never escapes, and call uses are readonly+nocapture stays a
   plain alloca instead of a dedicated gcframe slot. Zero-inits the alloca (memset) and
   strips lifetime markers since gcframe slots were null-initialized and code
   (e.g. @isdefined varboxes) may read-before-store.
   Measured: ef2 gcframe 27→20 (JL_ELIDE_MAX=-1). Slot map at 20: 2 header + 9 shared +
   4 dedicated (incl. 1 Unsafe return_roots buffer) + 5 colored.

## OPEN PROBLEM — unresolved crash (DO NOT TRUST current WIP as validated)

Reproducible-per-build, flaky-across-builds crash in `check_ef2.jl`
(`--compiled-modules=no`, loads JuliaLowering):

    ERROR: LoadError: FieldError: type typeof(Base.CoreLogging.logging_error) has no field `args`
      [1] getproperty(x::Function, f::Symbol)
      [2] macro expansion @ reflection.jl:1426   (= @invokelatest: `f = :(GlobalRef($s, ...))`)
      [3] fl_lower @ flfrontend.jl:24

Interpretation: during flisp lowering of a log-macro expansion (logging.jl:391
interpolates the `logging_error` function object into `@invokelatest`), the
`@isdefined(s)` at reflection.jl:1425 spuriously returned TRUE although `s` was never
assigned (isexpr(f,:.) false), so line 1426 did `f.args[2]` on a Function.
`s` is a maybe-undef boxed local ⇒ varbox slot ⇒ suspicion: something makes the varbox
read non-null garbage (varboxes may rely on gcframe null-init).

Evidence matrix (all same sysimage, built 2026-07-11 08:24 from b1a8fe0456 + WIP refinements):
- Build A (ungated elision):        crash ×2
- Build B (env-gated, no memset):   PASS ×7 (M=0, M=-1, 3× heap-hint stress, 2× JL_SLOT_MAP)
- Build C (added provenance print): crash at M=-1
- Build D (added memset init):      crash ×7 — **including M=0 (elision OFF) and poison/zero-init**

**RESOLVED 2026-07-11 (new machine): the matrix is explained by the persistent JIT
object cache (`src/objcache.cpp`), not by the pass logic.** The cache key is
SHA1(LLVM version, JL_CODEGEN_SRC_HASH, unoptimized-module bitcode hash) — the
`JL_ELIDE_*` env knobs change emitted code WITHOUT changing the key, so within one
build (one source hash), whichever run executed FIRST determined the cached object
for every function, and all later runs were served that object regardless of env:
- Build A: first runs had elision ON pre-zero-init (genuinely unsound: elided
  `@isdefined` varboxes read stack garbage instead of null) → poisoned objects cached
  → crash ×2. This IS the FieldError mechanism (spurious `@isdefined(s)`==true).
- Build B: first runs were M=0 → sound objects cached → all later runs (incl. M=-1)
  served sound parser/Base code → pass ×7.
- Build C: first run was M=-1 pre-zero-init → poisoned cache → crash.
- Build D: first runs were JL_ELIDE_POISON=1 → 0xDA-initialized varboxes cached →
  every later run crashed, including the M=0 "control" (never a real control).
⇒ The zero-init memset fix has never been cleanly tested (D's cache was pre-poisoned).
⇒ RULE for all A/B experiments with env-dependent codegen on this fork: run with
  `JULIA_OBJCACHE=0`, or point `JULIA_OBJCACHE_PATH` at a per-condition scratch dir.
  (Cache lives at `$DEPOT/cache/v<maj.min>/objcache`.)

VALIDATED on the new machine 2026-07-11 (all with JULIA_OBJCACHE=0):
- Zero-init elision clean ×many (incl. heap-hint stress); poison-init deterministically
  reproduces the original FieldError → zero-init is load-bearing, mechanism closed.
- JuliaLowering suite 9,753 pass / 76 broken (pre-existing) with elision on.

FURTHER OPTIMIZATIONS 2026-07-11 (new machine, per-change deltas on ef2):
1. gc_roots_begin was being DELETED BY DSE on single-root buffers (its argmem:write
   is fully clobbered by the subsequent real store). Declared it argmem:readwrite →
   markers survive → those buffers pack: gcframe 20→17, frame 3,312→3,216
   (compile 1,968→1,728).
2. Union-return convention pairing: calls returning {payload, selector} pass the
   payload buffer at operand 0 WITHOUT an sret attribute → SretAI was null → Unsafe.
   Now pair with a noalias+nocapture+non-readonly operand 0. (Beware: when the
   return_roots attr is on operand 0 itself — all-pointer srets — SretAI==SRet_gc
   must remain the no-pair no-unsafe case; do NOT require i>=1.)
3. PackReturnRootsBuffers::collectUsers walks select/phi users (union results select
   between box and stack payload); pair-skip (not bail) for tracked all-roots payload
   buffers (GC-visible, root their own contents): gcframe 17→16, ZERO dedicated
   allocas, frame 3,200 (compile 1,456).
4. Elision default ON (JL_ELIDE_MAX unset ⇒ -1); knob retained for bisection.
- ef2 gcframe now 16 = 2 header + 9 shared + 5 colored + 0 dedicated (was 272).
- Scaling litmus FLAT: 16/16/16 slots at M=1/2/4 arm duplication (was 28/39/47);
  machine frame still scales (3,200/5,520/10,128 B) — that is the non-GC stack side,
  i.e. the deferred lifetime.end/borrow-tracking project.
- Frame re-grounding on this machine matched the old machine exactly at parity builds.

CAMPAIGN CONCLUSION (2026-07-11): the gcframe is at its floor on the JuliaLowering
example. An LLVM_DEBUG-gated lower-bound check computes the slot-weighted max
concurrent liveness (a hard lower bound for the shared region): shared == bound for
every measured function (ef2 9=9, est_to_dst 21=21, vst1 7=7, compile_lambda 22=22),
i.e. first-fit packing is optimal here, the colored region is PEO-optimal on chordal
SSA interference, and the header is fixed. Further shrink requires changing actual
liveness, not packing.

MERGE-READINESS CHECKLIST — ALL DONE 2026-07-11:
- Debug env knobs stripped (8fb4d0f117): elision unconditional with zero-init;
  diagnostics folded into LLVM_DEBUG. No env-dependent codegen remains (objcache-safe).
- ColorRoots exactness invariant documented (8fb4d0f117).
- llvmpasses regression tests added (00fc65b55e): packing, union-return pairing,
  gc_roots_begin def-kill + deletion, elision + zero-init; gcroots.ll's
  @leftover_alloca updated to store a boxed value (arguments are now elided).
  Full llvmpasses suite green (pipeline-o2.jl fails only under lit's HOME=/tmp on
  this shared box — /tmp/.julia is owned by another user; passes with a private
  depot). Note: the "no safepoint after first unrefined def" gate skips placement
  entirely, so pure-elision test functions must also contain an unrefined root.
- clang static analysis (analyze-llvm-late-gc-lowering, analyze-codegen incl.
  cgutils) clean.
- Validation ladder complete: JuliaLowering suite 9,753 pass (both
  --compiled-modules=no and pkgimage runs, post-bootstrap); Base core 7,354,200
  pass; heap-hint stress clean; FULL BOOTSTRAP (sysimage + 108 stdlib pkgimage
  configurations) succeeded with the final knob-free pass; ef2 gcframe 16 confirmed
  on the bootstrapped image.
- NOT pushed, no PR (user instruction). When a PR is eventually opened, it must
  disclose generative-AI assistance (AGENTS.md).

MACHINE-FRAME PHASE (2026-07-11, commit 4c87e00ec4) — user-directed follow-on:
- Attribution via `llc -debug-only=stack-coloring` on the dumped post-opt module
  (libLLVM has asserts; per-function isolation needed because in-process JIT debug
  output interleaves across threads): of ef2's 406 stack slots / 7,416 B, 126 slots
  (2,464 B) had NO lifetime marker → Conservative → unmergeable. 101 of those were
  promotable `new::UnitRange` temporaries (cold throw_boundserror args) skipped by
  emit_new_struct's promotion guard.
- Fix: mark promotable news unconditionally; promotion RAUW sites
  (boxed() promotion, emit_new_struct field promotion) scrub lifetime intrinsics
  via erase_lifetime_intrinsics(); under promotion hazards the marker sits right
  after the alloca (dominates promotion-inserted stores; LifetimeStartOnFirstUse
  anchors the real range at first use).
- Results: StackColoring merges 376/406 slots (was 263), conservative 129→10.
  Frames: ef2 3,200→1,184 B (campaign total 9,760→1,184, −88%); est_to_dst
  5,296→2,816; vst1 3,152→2,256. Scaling litmus frame nearly flat:
  1,184/1,312/1,568 B at M=1/2/4 (was 3,200/5,520/10,128). Whole-pipeline stack
  high-water for lowering base/range.jl: ~19 KiB (was ~196 KiB post-step-1;
  ~260 KiB baseline) — reconstructed harness (gcframe-wip scratch highwater.jl).
- Validated: JuliaLowering suite 9,753 pass; Base core 7,354,200 pass; llvmpasses
  50/51 (pipeline-o2.jl environmental); clang static analysis clean; full bootstrap
  re-run with the change.
- CONSEQUENCE: the lifetime.end/borrow-tracking project is now LOW ROI — starts-only
  suffices once every alloca class is marked.

DOUBLING-RESIDUAL CHASE (2026-07-11, commit eaca3fd73c): the ~128 B/doubling litmus
growth was phi_result buffers (emit_phinode's copy of the edge-staging buffer at
each CFG merge) — the last unmarked-scaling class. Marked at the defining memcpy
(dominates all phi uses): litmus now 1,136/1,152/1,184 B at M=1/2/4 (~16 B/doubling).
Two lessons recorded:
1. Do NOT add a start to the phi edge-STAGING buffer (phi::): it is stored on loop
   back edges positioned after its lifetime.end; end-only markers merge fine
   (first-use anchoring + closing end), while start+end turns back-edge stores into
   out-of-region uses → Conservative → regression (measured: phi:: [C] 1→12 slots).
2. Remaining ~16 B/doubling is UPSTREAM: MemCpyOpt::performStackMoveOptzn merges
   memcpy-connected allocas and deletes both allocas' lifetime markers (verified by
   -print-after bisection: marker present after ADCE, gone after MemCpyOpt). An
   upstream fix could re-emit a start for the merged alloca. Also inherent:
   jlcallframe, gcframe, genuinely-overlapping slots.
Validation for eaca3fd73c: suite 9,753 pass; Base core 7,354,200 pass; static
analysis clean; bootstrap re-run. Attribution tooling: llc -debug-only=stack-coloring
on isolated module dumps + JULIA_LLVM_ARGS="-print-after=<pass> -filter-print-funcs=…"
(julia's no-op Marker passes bisect pipeline stages; in-process -debug-only output
interleaves across JIT threads, so always analyze isolated dumps with llc).

COLD-PATH LIFETIME ENDS (2026-07-12, commit ae5853ef40) — user-directed prototype:
- Mechanism (from StackColoring source + IR-surgery experiment): staging buffers for
  no-return calls (throw_boundserror args) are stored on the hot spine and read only
  in unreachable-terminated blocks. First-use liveness with no end runs to function
  exit, so every such buffer interferes with every later one along the spine (an end
  AFTER the throw does not help — block-level may-liveness leaks into the hot
  successor). The exact placement is ONE end on the NON-THROWING SIBLING EDGE; it is
  sound in loops because the read block's single predecessor holds every store
  (contents re-established after the kill), and single-end keeps first-use anchoring
  (2+ ends trip PR27903 → conservative → marker-driven, which requires complete
  markers).
- insertColdPathLifetimeEnds in llvm-late-gc-lowering (runs before the main pass
  work): v1 shape = all users analyzable, reads confined to ONE unreachable block Rb,
  single pred P holding all stores, cond branch → end at sibling top. NOTE: at pass
  time the call operand is an ADDRSPACECAST of the alloca (RemoveJuliaAddrspaces runs
  later) — the user walk must look through it (cost a debugging round: the opt
  harness on post-lowering dumps behaves differently from the in-pipeline IR).
- Results: ef2 frame 1,136→1,072 B flat across fan-out (1,072/1,088/1,120 at
  M=1/2/4); est_to_dst 2,512, compile 1,024, _convert_closures 1,408. Each end also
  collapses the merge groups (one patched slot absorbed 15-20 chained buffers).
  UnitRange slots 12→5 (survivors have shapes outside v1: multi-block stores, shared
  throw blocks, multiple read blocks).
- Validation: suite 9,753 pass; Base core 7,354,200 pass; heap-hint stress clean;
  llvmpasses green + new late-lower-gc-cold-lifetime-ends.ll; static analysis clean;
  bootstrap re-run.
- FOLLOW-UP options: extend v1 shapes (stores in dominating blocks, multi-pred read
  blocks via per-pred ends... beware multi-end conservative rule), or the store-
  SINKING variant (also removes 2 hot-path stores per bounds check — runtime win).

NEWSINK CHERRY-PICK (2026-07-12, JuliaLang/julia#60879 → commits 6f30a175d5,
5d46921cb1 + port 7c39cd9639): upstream's NewSink pass IS the sinking variant
(sinks error-path staging stores into the cold block; runs between MemCpyOpt and
DSE). Cherry-pick notes: (a) Makefile conflict — added llvm-newsink to BOTH
CODEGEN_SRCS and CODEGEN_SRCS_HASH (objcache key; upstream lacks it); (b) written
for an older CaptureTracker API — ported to LLVM 21's
Action captured(const Use*, UseCaptureInfo) (false→Continue, true→record+Stop).
A/B on ef2 frame (M=1/2/4):
  ends only     1,072 / 1,088 / 1,120
  NewSink only  1,088 / 1,120 / 1,168
  BOTH          1,072 / 1,088 / 1,088   ← strictly best; residual ~8 B/doubling
Complementary by mechanism: with NewSink active our insertColdPathLifetimeEnds
fires 25× (was 107) — sinking covers most shapes AND deletes the hot-path stores;
the ends catch NewSink's legality/profitability bails. Validation: suite 9,753
pass; Base core 7,354,200 pass; llvmpasses 70/71 (incl. the PR's 20 NewSink tests;
pipeline-o2.jl environmental); clang analysis clean; bootstrap re-run.
Upstream feedback for the PR: needs the LLVM 21 CaptureTracker port; measurably
better paired with cold-path lifetime ends than alone.

PRECISELIFETIMEENDS PASS (2026-07-13) — the general precise-ends analysis
(ENDS-DESIGN.md), motivated by the CFG-shape matrix (shapes.jl): straight-line and
in-loop code got ZERO slot merging under starts-only markers. Implementation notes
beyond the design doc:
1. The admission rule is reachability-based (no use forward-reachable from an
   inserted end without first passing the start), replacing the design's cruder
   single-def restriction — admits loops, rejects trailing dead stores and region
   re-entry.
2. TWO fixes discovered by ef2 regression (1,072→2,752 at first!): (a) suppress
   ends in unreachable-terminated blocks — they bound nothing, and a second end
   costs first-use anchoring; (b) reposition each candidate's lifetime.start to the
   NCD of its accesses — entry-block starts (promotion-hazard placement) make
   marker-driven conservative intervals span the whole function. Both are inherent
   to the PR27903 mode flip and belong in any upstreaming writeup.
3. Subsumes and removes insertColdPathLifetimeEnds; NewSink retained (hot-store
   removal).
Results: shapes matrix straight_16 352→112 B, pairs_16 608→128, loop_straight_16
352→112, loop_fanout_16 336→96 (control intact). JuliaLowering: ef2 1,072→736 B
(736/752/800 at M=1/2/4 — through the previous ~1,016 stackSize floor estimate,
mostly by collapsing spill pressure... to be attributed), vst1 2,208→1,088,
est_to_dst 2,512→1,280, compile 1,024→800, _convert_closures 1,392→992.
Validation: suite 9,753 pass; Base core 7,354,200 pass; heap-hint stress clean;
llvmpasses 70/71 (+ new precise-lifetime-ends.ll: straight-line/loop/cold-read/
both-paths/trailing-dead-store/region-reentry/escape cases); clang analysis clean;
bootstrap re-run with the pass active.

FORWARDER ENHANCEMENT (2026-07-13, separate commit per risk isolation): pointer
phis/selects over candidate buffers (SimplifyCFG sinking / if-conversion shapes)
modeled as forwarders with SSA-style EDGE SUBSTITUTION in the backward dataflow —
each pointer phi owns a liveness bit converted into the matching input's bit per
predecessor edge; selects generate the union of inputs. Placement uses carrier
liveness (own bit ∪ phi bits that may carry the candidate); admission counts
forwarder reads as uses of all carried candidates; forwarder escapes poison the
carried set. Known intentional loss vs code-level un-sinking: entangled buffers
never merge with each other, only with everything else.
Reproducers (gcframe-wip/phi_forwarder_scale.py raw-phi flavor;
phi_forwarder.jl if-converted select flavor via the real pipeline):
  raw:   88/280/1,048 B at N=4/16/64 → flat 40 B
  julia: 464/1,552 B at N=4/16 → 256/608 (2N srets collapse to 2 slots)
JuliaLowering: ef2 736→704 B (704/736/784 litmus), est_to_dst 1,280→1,248,
_convert_closures 992→944. Full ladder green (suite/core/stress/llvmpasses incl.
phi/select/poisoned forwarder lit cases/analysis/bootstrap).
RESIDUAL — CORRECTED ATTRIBUTION (the earlier "machine scheduler hoists LEAs"
explanation was WRONG): per-class marker census showed the ~23 B/unit residual was
MemCpyOpt's stack-move merging phi_result into phi:: for units 6+ and DELETING both
allocas' markers (the same root cause as the old ~16 B/doubling ef2 leak).
Markerless buffers bailed the pass's require-existing-start rule and got empty
StackColoring intervals → excluded from merging entirely.

START SYNTHESIS (2026-07-13, follow-up commit): the require-existing-start rule was
a proxy, not a need — for a fully-analyzable alloca with NO markers at all, the
pass now synthesizes the lifetime.start at the tight NCD-of-accesses position
(vacuously sound: no accesses precede it) and proceeds normally; foreign protocols
(existing ends, multi-start) still bail, and start-less candidates with only
forwarder-mediated accesses bail (nowhere to anchor). This makes the pass the
canonical end-of-pipeline lifetime authority, repairing anything mid-pipeline
passes strip. Results: Julia forwarder reproducer 256/608 → 160/256 (≈8 B/unit
left); ef2 704→688 B with litmus 688/704/720 (8 B/doubling, MemCpyOpt class
recovered); est_to_dst 1,248→1,008; compile 784→640; _convert_closures 944→864;
vst1 1,088 unchanged; shapes matrix and raw reproducer (flat 40 B) intact.
- A verbatim-copy MWE of @invokelatest (gcframe-wip/mwe_isdef2.jl) did NOT reproduce
  (now explained: fresh compiles never hit the poisoned cache entries).
- NOTE: incremental `make -C src` after header edits is unreliable (see
  llvm-gc-interface-passes.h dep gaps); when in doubt `make -C src clean && make -j`.

DEFERRED + DEFAULT-ON MARKER EMISSION (2026-07-13, amended into the lifetime.start
commit during the review rebase): two revisions to the frontend marker scheme.
(1) DEFERRED: instead of emitting markers eagerly and scrubbing them at every
promotion RAUW site (erase_lifetime_intrinsics — a silent-miscompile footgun for
future promotion sites), allocas are recorded as WeakVH and markers are emitted in
one sweep at the end of emit_function; promotion erases the alloca, nulling the
handle, so promoted temporaries drop out with no coordination. Verified identical
output to the eager scheme at the commit-2-only point; at full-stack tip the
census shifted ±100 B bidirectionally (net −48 B; marker-position-sensitive
mid-pipeline transforms) with litmus DEAD FLAT 752/736/752.
(2) DEFAULT-ON: emit_static_alloca records every alloca by default; opt-outs
(lifetime=false) only for GC-scanned buffers (emit_static_roots, the
value_to_pointer inline-roots reassembly buffer) and buffers with their own marker
protocols (phi edge-staging with per-edge starts, ehbuff) where a second start
would flip PR27903 conservative mode. A/B at commit-2-only (per methodology: the
late pass masks the effect at tip): the ONLY real coverage gap was ccall/sret
buffers (escaping allocas the late pass must always bail on — gap_shapes.jl
ccall_sret 160/544 B at N=4/16 → flat 96/96); union-typed shapes were already
flat via SROA (never a gap). JuliaLowering census cost: ±16 B. This cleanly
separates the two optimizations: frontend markers = by-construction privacy
(covers escapes), PreciseLifetimeEnds = IR analysis (covers everything visible).

MEASUREMENT HAZARD — PKGIMAGE STALENESS (2026-07-13): code_native/code_llvm on a
method loaded from a pkgimage DISASSEMBLE THE CACHED CODE, and pkgimage validity
does not key on libjulia-codegen contents — after `make -C src` at a different
commit, cb3.jl-style censuses of package functions silently report the OLD build
(signature: package-function numbers exactly match a previous build while fresh
@eval reproducers move). ALL cross-build censuses must run with
--compiled-modules=no. Fresh-compile re-measurement corrected the record:
pre-campaign baseline ef2 9,760 / vst1 11,712 / est 12,112 / compile 5,760 /
_convert_closures 4,896, high-water ~259 KiB; commit-2 (markers-only,
deferred+default-on) 3,200 / 4,720 / 5,296 / 2,864 / 2,832, high-water ~131 KiB,
litmus 3,200/5,280/9,424 (gcframe 272/529/1,043 — GC-frame scaling is PR 2's job).
Tip census numbers quoted in older sections above were pkgimage-tainted in some
runs; re-verify with --compiled-modules=no before quoting externally.

ZERO-RESTORATION (2026-07-13, isolated commit — measurable cost): when a packed
shared slot's occupant dies (within-block death or region-exit edge), the packing
now re-zeros the occupant's frame words so the GC never scans a dead occupant's
stale roots — the "borrow requires restore" discipline from the design-origin
Slack thread, making shared slots observationally identical to dedicated
zero-initialized slots. Placement mirrors LiveRanges: after the last use for
within-block deaths (skipping terminators), at tops of non-live successor blocks
for region exits, suppressed into unreachable-terminated blocks and when a
co-occupant of the same slot is already live-in (its store would be clobbered
anyway and zeroing would kill ITS root). ef2 gets 793 restore stores; frames
unchanged; lowering benchmark cost ≈2% (see benchmark record below). GC precision
gain: dead occupants no longer retained until the next borrower's store.

NEWSINK A/B + DROP (2026-07-13): measured the full stack with NewSink disabled
(pass registration commented out, rebuild, JULIA_OBJCACHE=0):
  shapes matrix: identical except loop_straight 112→128, loop_fanout_4 96→112
  forwarder reproducers: identical (raw flat 40 B; julia 160/176)
  cb3: ef2 688 identical; est_to_dst 992 (vs 1,008); compile 656 (vs 640) — ±16 B
  bench_lowering.jl: 91.6/161.4/22.7 ms min vs 91.4/162.6/22.8 — statistically
  identical
Conclusion: after PreciseLifetimeEnds + forwarders + start synthesis, NewSink
contributes nothing measurable to stack size or lowering wall time here (its
remaining value is hot-path store deletion in bounds-check-heavy numeric code,
not exercised by lowering). DECISION (user): DROPPED the three cherry-pick
commits from the branch (rebase; conflicts only where PreciseLifetimeEnds hunks
abutted NewSink lines in src/Makefile and src/passes.h) — upstream JuliaLang/julia#60879
proceeds as an independent initiative. The cherry-pick evaluation record above is
retained for history; its commit hashes no longer exist on this branch. If it is
ever re-picked: needs the LLVM 21 CaptureTracker port and the CODEGEN_SRCS_HASH
Makefile entry (objcache key) noted above.

BEFORE/AFTER BENCHMARK (2026-07-13, gcframe-wip/bench_lowering.jl, 15 samples
min/median ms over range.jl / abstractarray.jl / strings/string.jl, worktree
JL_stack_benchbase @ 6c69a8c12e = pre-campaign baseline, JULIA_OBJCACHE=0,
--compiled-modules=no):
  baseline (pre-campaign):  95.4/97.1   171.9/174.8   24.5/24.9
  campaign tip pre-zeroing: 88.8/89.3   158.8/160.9   22.4/22.8   (~7-9% faster)
  + zero-restoration:       91.4/91.9   162.6/164.8   22.8/23.2   (~2% given back)
The speedup tracks the stack work (frames 9,760→688, gcframe 272→16, high-water
~260→~19 KiB), not NewSink (identical without it).

## Scripts in this directory
- `check_ef2.jl` — ef2 gcframe slot count + return_roots census (primary metric)
- `cb3.jl` — frame-size measurement, top-5 JuliaLowering functions
- `scale_real.jl` — real expand_forms_2 arm-duplication litmus (M=1/2/4)
- `scale_test.jl`, `scale_test_compat.jl` — synthetic N-way dispatch litmus
- `mwe_isdef2.jl` — @invokelatest fresh-JIT MWE attempt (does not reproduce)

Debug env knobs in the WIP pass: `JL_ELIDE_MAX` (0=off default, -1=all, N=first N),
`JL_ELIDE_POISON` (0xDA fill instead of zero), `JL_SLOT_MAP`, `JL_REFINE_DUMP`.

## Queue after crash is resolved
- Explain/eliminate residual dedicated slots (Unsafe phi-merged return_roots buffer via
  range-union packing); fresh vst1/est_to_dst censuses; residual M-scaling growth
  (per-arm promotable news, [min,max] interval merging).
- Strip all debug prints/knobs; validation ladder: JuliaLowering suite
  (--compiled-modules=no), Base core tests, 100M heap-hint stress, full bootstrap.
- Deferred (user-approved): const-field TBAA follow-up (cgutils.cpp best_field_tbaa);
  llvm.lifetime.end / borrow-tracking; B3 upstreaming chores (llvmpasses tests incl.
  scaling litmus, ColorRoots SSA-invariant comment, AI disclosure on PR).
