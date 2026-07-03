# Function-splitting investigation notes

## COMPLETE PICTURE (synthesis, 2026-07-02)

Every super-linear compile cost observed is a named mechanism, each confirmed
by profiling/attribution + a kill-test or scaling check:

| shape of oversized function | dominant unsplit cost | evidence |
|---|---|---|
| giant straightline block (float) | SLPVectorizer ~cubic (40% at 64k; 240s at 128k) + ISel quadratic | -time-passes at 2 sizes; -vectorize-slp=false: 34.6->9.8s |
| giant block of calls (rooted values live across) | GreedyRegisterAllocator ~quadratic (87% = 92s at 32k calls) | -time-passes |
| huge branchy CFG, call+root heavy (stock ReverseDiff) | BlockFrequency + IRCE + GVN superlinear on ~10k-block CFGs (~60s of 89s at N=10) | -time-passes |
| any: calls in huge blocks | InstCombine isKnownNonZero -> renumberInstructions O(calls x blocksize) | gdb sampling 24/24; FIXED by pre-InstCombine pass position |

Splitting bounds all of them per region. Runtime effects of splitting:

1. Boundary tax (call-free code only): ~10-12ns/boundary marshalling constant
   (call/ret, arg pushes, vzeroupper, 8x store-load round trip, selector),
   total = boundaries x constant. Call-heavy code: boundaries are FREE
   (runtime flat from c200 through unsplit at 16k calls).
   PMU attribution DONE 2026-07-02 on Zen 4 (PERF.md "RESULTS"): the constant
   is pure marshalling instructions at UNCHANGED IPC (64k split = 2.52 vs
   2.51 unsplit); the super-linear term is demand L1i fills sourced beyond L2
   (~8-10 cyc each; prefetch-hidden when unsplit — unsplit-256k streams 5.5k
   sys fills/iter at IPC 2.34 — demand-exposed at region entry/exit) plus a
   secondary BTB/indirect-target capacity term (5-10 mispredicts+resteers per
   boundary at 256k); iTLB refuted (<=10-15% priced at full walk latency).
   Reframing: per-boundary normalization misleads once footprint >> L2 —
   penalty/iter ~= marshalling/IPC + ~9cyc x demand code fills, where fills
   track FOOTPRINT streamed per iteration; boundary count enters mainly by
   inflating footprint (+118 insts each). Fewer, larger regions on call-free
   code — now with the mechanism attached.
2. Code-size/front-end term: post-opt module size varies up to 72% with CUT
   PHASE because SLP vector width is decided by store-seed adjacency — the
   output-spill stores of the 8 chains form contiguous 4-wide seeds only for
   some cut spacings (256k: c565/c1600 -> 223-224k insts, 20-25us; c400/c800
   -> 369-385k insts, 36-49us; identical 595,840 before-insts). Runtime of
   once-through code tracks final code size, not boundary count.
3. [ADL-specific, does NOT reproduce on Zen 4 — runtime identical at the FMA
   bound there; Zen 4's decode sustains the 2-wide stream (74% backend-bound,
   op-cache miss but IPC-neutral). SLP's ~cubic COMPILE cost reproduces on
   both: 39.5s vs 14.1s.] SLP seed effect can make splitting a runtime WIN
   on straightline float (on ADL):
   unsplit has only a scalar reduction sink -> 2-wide (at every size 1k-32k);
   store-seed probe: same block with array-store sink -> 4-wide. Split regions
   end in aggregate stores -> 4-wide -> unsplit 13.4us vs split 8.0us at 64k.
   (Also: -vectorize-slp=false runtime 6.8us — SLP 2-wide is a pessimization.)

Compile-time vs region size R (realized, instrumented; per shape):
- call-free branchy: flat plateau R in [1600, 25600] (both 64k and 256k),
  mild rise at R=400, gentle right arm 25.6k->64k, unsplit 1.6-4.7x plateau.
- call-heavy: strictly increasing in R (RA per-region superlinear);
  best at smallest sampled R (~200), no left-arm penalty.
- runtime asymptotes to unsplit as R grows (no U); penalty ~ (S/R) x 10-12ns
  + the cut-phase code-size term (dominates when it triggers).

Trade-off summary: region size wants to be SMALL for call/root-heavy code
(compile: RA) with zero runtime cost, and LARGE for call-free dense code
(runtime: boundary tax) where compile is plateau-flat anyway. These do not
conflict: a dual cap (grow until N insts OR M safepoints, whichever first)
serves both. The cut-phase/SLP-seed sensitivity is the one genuinely new
design input: cut placement in straightline code should prefer boundaries
that keep vector chains packable (or at least sweeps must treat cut-phase as
a variance source of up to 2x runtime on chain-structured code).

Fixed/landed along the way: pre-InstCombine pass position; O(n) chunk
splitting; clamp cuts + realized-size logging (-julia-split-time);
MaxBlocks 512->4096 flag; aggregate output marshalling (output-spill-min=2,
0-19% + it is what creates SLP store seeds); eh_state attribute pinning;
return_roots pinning; single-exit-cuts diagnostic flag (not beneficial).
Validation (65536/4096/400): tracked N=20 45.8->9.3s, stock N=10 99->25.5s,
MTK build 70.5 vs 66.9s (no overhead), all correctness checks pass.

Open (explicitly not load-bearing): exact SLP width-heuristic internals;
which modulo relationship makes c565/c1600 phase well; front-end
cost model constant (~0.1ns per once-through instruction).

Working notes for the open sub-investigations (task list mirrors these).
Machine: WSL2, 20 vcores, power profile changed 2026-07-02 (all numbers after that).
Protocol: every runtime number is min-of-reps within one process; cross-process
variance observed at ±15-20% (code layout/ASLR), so single-run deltas below ~20%
are treated as noise unless replicated. Compile numbers repeat to ~±10%.

## Established (confirmed mechanisms)

- **InstCombine quadratic on huge blocks (fixed)**: visitCallBase → isKnownNonZero →
  comesBefore → BasicBlock::renumberInstructions, O(calls × block size).
  Confirmed by gdb stack sampling (24/24 samples). Fixed by running the splitting
  pass before all InstCombines (pipeline.cpp) — LLVM time went superlinear→linear
  (N=48 reversediff: 425s → 98s total).
- **chunkBlock splice quadratic (fixed)**: front-to-back splitBasicBlock moved the
  whole tail per cut; now back-to-front, O(n).
- **Boundary cost is real and latency-flavored**: per region transition on the
  branchy call-free float shape ≈ 17-25ns (~70-100 cycles). Confirmed components
  from asm reading: store-to-load round-trip per live value, duplicated
  data-dependent exit-selector branch (`test al,1; je`), call/ret + push-heavy
  frames, vzeroupper per call, scalar↔vector repacking. Shares NOT yet decomposed
  (task 4). Aggregate output marshalling (output-spill-min=2) reduced instruction
  count but only −9%@128k / −19%@256k, nothing ≤64k ⇒ latency-bound, not
  throughput-bound.
- **Region-growth clamp artifacts (instrumented)**: MaxBlocks=512 caps regions at
  ~5-7k insts on small-block CFGs (Julia lowering makes a 40-stmt diamond ≈ 3
  blocks of ~13-20 insts); at target 64000, MinSize=Target/4=16000 is unreachable
  within the clamp → growRegion returns false → **0 regions formed** → the
  "c64000" datapoint was actually unsplit (matches off: 6.0≈5.9s, 4.20≈4.27µs).
  The apparent plateau ≥6400 was the knob saturating, not economics.
  Now: -julia-split-max-region-blocks flag + realized size min/med/max +
  cut(target/clamp) + growfail(blocks/size/stuck) counters under -julia-split-time.
- **Benchmark confound (mine)**: blocks() executes only ~one arm per diamond ⇒
  ~S/2 executed ops vs straight()'s S. Cross-generator runtime comparisons at
  equal S were 2× off. Corrected per-executed-op view:
  - blocks-off ≈ FMA latency bound (~0.13ns/op). straight-off ≈ 1.7× over bound.
  - straight-ON recovers the bound; blocks-ON ≈ 1.75× over (boundary tax).
- **Giant-block runtime penalty is NOT regalloc spills**: unsplit straight-64k has
  0 spills/reloads. It emits 32,768 FMAs for 65,536 muladds (2-wide xmm) vs
  4-wide ymm in split regions ⇒ 2× dynamic instructions, ~650KB straightline code
  streamed per call ⇒ front-end bound. (Earlier "register allocator poison" claim
  was wrong.) SLP width degradation mechanism = task 2.
- **EH-state frame requirement**: enter/pop handler calls restore ct->gcstack
  snapshots valid only if GC-frame pushes since enter were popped; an outlined
  callee's own GC frame violates this (hit as rtutils.c:338 assert via @timed
  thunk splitting). Fixed structurally: "julia.eh_state" fn attr on the 6 EH
  runtime declarations in codegen.cpp; isPinned keys on the attribute.
  (Old name-based pinning had never matched: IR symbols carry the ijl_ rename.)
- **return_roots callsites pinned**: buffer must be an alloca in the callsite's
  function (LateLowerGCFrame aborts otherwise) and must outlive sret reads;
  pinning is sounder than per-region privatization (region-local buffer dies at
  region return while sret memory may still hold the only reference).

## Parameter data so far (subject to the caveats above)

- block-threshold: single-block functions win from ~2k (float) / ~1k (calls) with
  runtime neutral-or-better ⇒ default 4096 proposed.
- chunk 400 validated on straight/calls (200-800 flat optimum); branchy call-free
  prefers larger realized regions (400→3200: 7.0→4.6µs vs off 4.27) — re-verify
  on realized sizes (task 3).
- group-size 8/24/64 indistinguishable at ~330 regions.
- function-threshold: call-heavy crossover ~4-8k, zero runtime cost; branchy
  call-free crossover ~50k with ~1.75× runtime tax ⇒ 65536 plain, or call-density
  gate, or adaptive region target (insts OR safepoints cap) — decide in task 8.
- Composite validation (defaults 65536/4096/400): tracked N=20 42.8→9.0s,
  stock N=10 94.5→24.9s, MTK build guard 72.5s vs 72.6s (no overhead, no crash).
  Late rows contaminated (concurrent rebuild/A-B) → rerun = task 6.

## Task 1 (DONE): giant-block compile blowup = SLPVectorizer, ~cubic

-time-passes on unsplit straight: SLP 3.14s@32k -> 24.1s@64k (7.7x per 2x,
40% of compile); ISel quadratic behind it (1.5 -> 6.1s). Kill test:
-vectorize-slp=false drops compile 34.6 -> 9.8s (opt pipeline 24.3 -> 0.83s)
AND improves runtime 13.4 -> 6.8us. On giant blocks SLP spends cubic time
producing 2x-slower code (2-wide packing + doubled code footprint).
Splitting before SLP both avoids the compile cost and yields better code
(split regions vectorize 4-wide, hit the FMA latency bound).

## Task 2 (CLOSED): SLP width mechanism unidentified, hypotheses refuted

-slp-schedule-budget=1e7 and -slp-max-look-ahead-depth=32 both still produce
2-wide packing on the 64k block. Whatever heuristic degrades width, it is not
those budgets. Not load-bearing for the pass (conclusion of task 1 stands);
flagged as an upstream LLVM curiosity.

## Task 3 (DONE): honest region-size axis (realized sizes, 3 reps)

With -julia-split-max-region-blocks=8192, realized sizes match targets
(instrumentation confirms; e.g. c25600 -> 6 x 25627 at 64k). blocks shape:
- Runtime: NO U — monotone asymptote to unsplit. 64k: 7.2/5.1/4.4/4.5/4.3us
  (c400/1600/6400/12800/25600) vs off 4.16. 256k: 50.6/20.0/17.7/16.8/16.4
  vs off 16.2. Penalty ~ boundaries x 10-26ns.
- Compile: broad flat bottom 1600-25600 (64k: ~3.5s; 256k: ~15-18s), mild
  rise at c400, unsplit 1.6x (64k) / 4.7x (256k) above the plateau. Call-free
  right-arm upturn is somewhere >25.6k (unsampled before due to clamp).
- Terminology fix: "julia-side" in the harness = frontend + LLVM BACKEND;
  the unsplit-256k quadratic (~50s) is the backend (ISel et al).
- Contrast: call-heavy compile upturn arrives ~3200 (earlier data) — per-shape
  optima genuinely differ; motivates insts-OR-safepoints dual cap.

## Task 4 (DONE): boundary decomposition — selector not the lever

Single-exit-cut preference (-julia-split-single-exit-cuts, kept as diagnostic)
was structurally a no-op on the branchy shape: cuts already landed on
reconvergence points (89 regions, ~same sizes), runtime unchanged within noise
(5.43 vs 5.58us medians over 3 reps), compile +15% from longer growth searches.
The `test al,1` selectors in the c400 asm come from hierarchical parent glue,
not leaf cuts. Combined with the aggregate-marshalling result (task earlier:
-9..19% only at >=128k), the per-boundary cost (~10-26ns) has no single
dominant removable component — the effective lever is boundary COUNT.
Do not adopt single-exit cuts.

## Task 7 (DONE): MaxBlocks default + clamp-cut fix

MaxBlocks default 512 -> 4096 (flag -julia-split-max-region-blocks), and
clamp-stopped growth now takes the best legal cut even below MinSize=Target/4
(previously: silently formed 0 regions when MinSize was unreachable inside the
clamp). Verified: blocks-64k @ target 64000 now forms 3 regions (was 0);
runtime = unsplit; compile 4.3s — above the 3.5s plateau, corroborating the
compile right-arm upturn between ~25.6k and ~64k for call-free code.

## Task 9 (DONE): privatization 0-candidates is legitimate

Alloca census of unoptimized IR: the stock megafunction has 477 SCALAR
`ptr addrspace(10)` allocas and no tracked arrays (all dispatch is static;
no jlcall arg-array buffers). At the pass's early position SROA/EarlyCSE have
already promoted those scalars to SSA -> zero tracked allocas remain -> zero
candidates. Fixed shape: no tracked allocas at all. Privatization remains live
for dynamic-dispatch functions (IndexCache-style [7 x ptr as(10)] buffers).
Diagnostic now prints privatized/candidates and notes silent skip classes.

## Task log

- [x] 1 SLP attribution
- [x] 2 SLP width mechanism (closed, hypotheses refuted)
- [x] 3 realized-size axis rerun
- [x] 4 boundary decomposition (selector ruled out; lever = boundary count)
- [x] 5 generator confound (ns_per_op column, REPS protocol)
- [ ] 6 clean validation rerun (running: 65536/4096/400)
- [x] 7 MaxBlocks 4096 + clamp cuts instead of silent no-op
- [ ] 8 finalize defaults + docs + whitespace + clang static analysis
- [x] 9 privatization 0-candidates legitimate (SROA promotes scalars pre-pass)

## Boundary-delta static examination (post-commit addendum)

SLP-off, c400, 64k vs 256k: per-boundary asm identical (~118 insts constant);
root glue frames 776B / 264B — spill structs are sunk into parent frames
(data side L1-resident per parent, ~1KB); hierarchy 2 vs 3 levels (bounds a
~10% effect via cross-parent transitions). Nothing static accounts for the
11ns -> 35ns per-boundary growth; the delta is dynamic fetch behavior of the
2.0MB vs 8.2MB once-through code footprint at prefetch-breaking region
entries. PMU experiment (PERF.md) is the discriminator: L1i/L2 residency vs
iTLB vs BTB.

## Boundary-delta: layout, code-model, and site-count probes (addendum 2)

- JIT layout (from module function-list order): root, then all parent glue
  clustered, then per-parent leaf bands — execution is 2-3 interleaved
  sequential streams, not scattered jumps.
- All region calls are INDIRECT (movabs+call rax): x86-64 JIT hardwires
  CodeModel::Large. Flipping to Medium crashes (Pointer32Signed relocations
  to anonymous data out of range of JIT allocations) — direct calls would
  need allocator colocation, not a code-model flip.
- Site-count (indirect-BTB) hypothesis REFUTED: SLP-off 256k, c565 (914
  sites, 7.1MB) = 18.8ns/boundary vs c800 (711 sites, 7.7MB) = 23.4ns —
  ordering follows footprint, not sites.
- Surviving model: per-boundary = ~10ns marshalling + fetch term monotone in
  total once-through code footprint (~4ns @6.9MB -> ~25ns @8.2MB), boundary
  count only multiplies. PMU task: confirm L1i/L2 vs iTLB at region entries.

## A/C coupling: direct calls restore fetch-ahead (other session, Zen 4, 2026-07-03)

CodeModel::Medium + Reloc::PIC_ on x86-64 makes region calls direct
`call rel32` (plain Static+Medium fails: jump tables emit R_X86_64_32S
assuming the low 2GB — presumably why Large was chosen). Bit-identical
results, 0 movabs. Per-boundary at 256k, Large -> direct:
- c1600: 170 -> ~37ns; branch-misses 10 -> 0.27; resteers 9.1 -> 0.37;
  demand L3 code fills 65.6 -> 19.9 (70% of the "residency" term vanished).
  Per-iter penalty 54.6 -> 11.9us with zero pass changes.
- c400: 81 -> ~75ns, fills ~unchanged — thousands of sites overflow the BTB;
  misses become decode-resteers instead of execute-flushes but the fetcher
  still cannot run ahead. Capacity, not predictability.
- 64k: c400 20 -> 12ns; c1600 ~7ns unchanged = irreducible marshalling core.

Mechanism: with a statically-known target the decoupled front-end fetches
across the boundary ahead of execution, so region-entry lines are prefetches
again; the indirect (Large-model) calls were what demand-exposed the icache
misses. A ("residency") was largely downstream of C (target opacity), up to
BTB capacity. New design constraint: keep region count per function within
predictor capacity (~hundreds, not thousands).

## Software code-prefetch REFUTED (other session, Zen 4, 2026-07-03)

32-line lookahead prefetch of the next region, measured under the Large
model: at c400 it converted a third of the from-L3 code fills into from-L2
fills — counters prove the lines arrived — yet cycles were UNCHANGED: in the
BTB-overflow regime the front-end is serialized on miss resteers, so the
fetcher's problem is not fill latency but not knowing where to go; cheaper
fills do not help. At c1600 it is a 13-21% regression (instruction overhead
plus pollution where BTB-steered fetch-ahead already works). Not a viable
lever in either regime. Sharpens the model: in overflow, target resolution
(control) gates fetch, not data movement — consistent with the A/C coupling.
Remaining levers: capacity-aware region sizing (deciding sweep pending) and
direct-call emission (Medium+PIC).

## OPEN: failed asymptote on branch-free chain code (see FAILED_ASYMPTOTE.md)

Split straight-shape code (SLP off) never converges to unsplit as regions
grow — 3.5x at a SINGLE boundary (c51200). Not boundaries, not code size
(module insts identical), not block size (unsplit scan monotone-good), not
MISched/SDAG-sched (flag-nulled). Machine code of pass-produced functions is
CHAIN-GROUPED (runs of 1420-1600 FMAs on one accumulator vs 8-way source
interleave) => latency serialization. Producer unknown; handed to the Zen
machine (FAILED_ASYMPTOTE.md, scripts in asymptote/). With SLP on this shape
is flat, and branchy converges — sizing conclusions stand — but this is the
one known case where split code is pessimized without a structural limit.

## RESOLVED + DIRECTION REVISED: seam sinking fixed (2026-07-03)

FAILED_ASYMPTOTE.md is now SOLVED (Zen root cause: InstCombine
TryToSinkInstruction cascading whole dependency chains across the pass's
unconditional seams, chain-grouping them; run length = chunk/8 => damage
grew with region size). Fix: mergeStraightSeams + caller call-block merge
in processLevel (822b725af3). ADL post-fix verification:

- straight SLP-off: FLAT 0.114-0.120 ns/op at every chunk 400..51200,
  BEATING unsplit (0.145) everywhere. The old "branch-free prefers small
  regions" (incl. the original chunk-sweep optimum at 400-800) was this
  artifact end to end.
- blocks tax unchanged: 64k ~12ns/boundary, 256k c1600 ~16ns, c400-256k
  still BTB-overflow-dominated. Sinking was never the branchy story.

Sizing direction is now UNIFORM: no call-free shape pulls toward small
regions. Call-free (branchy or straight) -> large regions (runtime tax ~
boundary count; compile flat to ~25k; BTB sites favor large too);
call-heavy -> small regions (GreedyRA compile), runtime-indifferent.
Dual cap reconciles; the instruction-side cap should be set well above the
old chunk-sweep optimum, and block-cut spacing (chunk) decouples from the
region target.

## Scheduler indifference explained (2026-07-03, ADL; within-batch comparisons)

2x2 + grouped-source probes (straight 65536, SLP off; machine drifted between
batches — compare within batch only):
- interleaved source: misched default = forced-on = 0.170 ns/op. Forcing the
  scheduler does NOT undo good order (pressure heuristic acts only on excess;
  the interleave sits at the 16-xmm limit without crossing it).
- split c6400: default 0.171 -> forced-on 0.141 (18% better!) — MISched IS
  disabled by default on x86 (target opt-in); forced on, it engages
  tractable-size region functions but is inert on the 65k monolith.
- grouped SOURCE (chains emitted one at a time, no pass involved): 1.321
  ns/op default, 1.336 forced-on — 7.8x worse than interleaved, and NOTHING
  in the pipeline repairs it, even forced. Dose-response confirms the
  mechanism: source-grouped runs of 8192 -> 7.8x; pass-induced runs of
  ~1400-1600 -> 2.5-3.5x.

Conclusions: "MISched expresses no preference" = it is not running (default
x86) or not engaging blocks this size (forced, 65k). IR instruction order is
fully load-bearing for ILP on x86: frontend/source order decides, InstCombine
may scramble it, and no default pass can recreate it. This is the strongest
justification yet for the order-preserving-sink upstream patch (lost order is
unrecoverable), and flags two curiosities: -enable-misched=true won 18% on
split region functions (a possible cheap knob for split code), and AArch64
(MISched on by default) may not exhibit the sinking pathology's full cost.

## CORRECTION to the scheduler section above (2026-07-03)

User's physics objection was right: a disabled pass cannot bill 1.9s.
Replication (3 reps, default/=true/=false in one batch): compile time
default==true (5.2-6.1s) vs =false (-1.4s) => MISched RUNS BY DEFAULT on
x86; "disabled by default" is retracted. The "18% -enable-misched=true win"
is also retracted: runtimes are BIMODAL across all configs (~11.2us vs
~7.6-9.2us, flag-independent) — almost certainly P-core/E-core scheduling
lottery on the 12700H under WSL2 (no pinning in gen_axes runs; perf_one.sh
pins, plain runs do not). This also explains earlier "session drift".
PROTOCOL FIX: pin benchmark runs (taskset -c <P-core>) from now on.
The load-bearing-order conclusion SURVIVES and strengthens: MISched runs and
still preserves grouped order (the 7.8x grouped-source probe had it active).

## DESIGN DECISION (user, 2026-07-03): seams accepted beyond merge limits

Block-merging proceeds up to the size limits our heuristics justify (SLP
knee: flat to ~3.2k, gentle to ~12.8k, cubic >=25k); seams are allowed to
appear beyond that. The InstCombine sinking interaction on residual seams is
accepted as a rare, specific scheduling issue marked for later follow-up —
the order-preserving-sink upstream patch is the eventual fix, not a blocker.
Block-size and region-size ceilings remain independent knobs with the seam
risk consciously accepted.
