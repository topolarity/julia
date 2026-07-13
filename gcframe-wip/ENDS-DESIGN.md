# Design: PreciseLifetimeEnds pass

Goal: give StackColoring exact live intervals for private stack buffers in ALL CFG
shapes (straight-line, loops, fan-out-in-loop) by inserting `lifetime.end` markers
derived from real dataflow liveness — replacing the shape-specific
`insertColdPathLifetimeEnds` and fixing the two measured failure modes
(gcframe-wip/shapes.jl): sequential call results never merge, and loop back edges
defeat the reachability-anchored merge test entirely.

## Placement in the pipeline

A standalone function pass (`llvm-lifetime-ends.cpp`, ~350–450 lines), registered in
llvm-julia-passes.inc and inserted in the lowering pipeline immediately before
LateLowerGCPass. Rationale: after all mid-level optimization (nothing downstream
deletes or invalidates markers — verified empirically for the cold-path ends), and
independently testable via opt. Must be added to both CODEGEN_SRCS and
CODEGEN_SRCS_HASH (objcache key).

## Candidate identification (bail-fast walk, same family as collectUsers)

Static allocas in the entry block, EXCLUDING tracked (addrspace(10)) element types —
those belong to the GC frame packer. Walk users through GEP/bitcast/addrspacecast:

- load                                → READ
- store (buffer = pointer operand)    → WRITE; a full-clobber KILL only if it covers
                                        the entire alloca (constant size, offset 0);
                                        otherwise neither generates nor kills
- memset/memcpy with buffer as dest   → WRITE; KILL iff constant full-size at offset 0
- memcpy with buffer as source        → READ
- call, buffer as arg operand:
    * sret operand                    → KILL (callee fully initializes) + not a read
    * readonly + nocapture            → READ
    * writable nocapture (non-sret)   → READ + WRITE, no kill (conservative)
    * anything else (captures, bundles) → BAIL
- existing lifetime.start             → KILL (contents undef above it); must be
                                        unique and dominate every READ, else BAIL
- existing lifetime.end               → owned by us (phi staging / cold-path v1):
                                        v1 BAILs on these allocas (phi:: multi-def
                                        buffers keep their current handling)
- store OF the buffer address, phi/select users, atomics, unknown → BAIL

v1 additionally requires a SINGLE static full-clobber def (the sret call or the one
staging sequence). This covers the measured pessimization classes — per-call-site
sret buffers and staging temps, in straight-line code and loops — while sidestepping
multi-region marker balancing (v2, below). Functions containing returns_twice calls
are skipped entirely.

## Liveness

Per-candidate backward may-liveness, structurally identical to
PackReturnRootsBuffers' Events machinery (which is this exact analysis specialized
to roots buffers): READS generate, KILLS stop propagation; per-block Begin/End event
positions; standard bitvector dataflow over the blocks that contain events plus
whatever the worklist reaches. Cost is the same order as the packer and ComputeLiveness.

## End placement

For each candidate with computed liveness:
1. Within-block death: if a block has a last READ at position p and the candidate is
   not live-out, insert one end immediately after p.
2. Region-exit blocks: for every block S with liveIn(S) = false that has a
   predecessor with liveOut = true, insert one end at S's first insertion point
   (covers all incoming edges at once; sound because liveIn(S) = false means no
   path from S reaches a read without an intervening kill).

Soundness invariant (assert in tests): an end at P is legal iff no READ is reachable
from P without a full clobber of the whole alloca in between — which is precisely
"backward liveness is dead at P".

## StackColoring interaction (the PR27903 trade-off)

- 1 end (static): first-use anchoring stays enabled; intervals are use-anchored and
  end-bounded. Ideal.
- ≥2 ends (single region with multiple exit blocks): the slot becomes "conservative"
  → marker-driven intervals. That is still exact and sound because our start + ends
  delimit the true region (conservative means "trust the markers", and ours are
  complete). One caveat: buffers whose start was placed at function entry (the
  args_may_promote hazard class) get [entry → ends] intervals in this mode — wider
  than first-use but still bounded; acceptable, noted for tuning.
- v2 (only if measurements justify): multi-region buffers via BALANCED region
  markers — a lifetime.start at each region re-entry (full-clobber def) paired with
  region-exit ends. Marker-driven conservative mode handles multi-segment intervals
  correctly when regions are balanced; unbalanced multi-region is the one truly
  unsound shape and is why v1 bails instead.

## Interactions

- Subsumes insertColdPathLifetimeEnds (its shape falls out of the dataflow:
  liveOut(store block) = true on the cold edge, liveIn(hot sibling) = false → end at
  sibling top). Delete it with the new pass.
- NewSink stays: it removes hot-path stores (runtime win) and runs mid-pipeline;
  this pass covers what sinking can't move.
- GC frame packer and elision: untouched (tracked allocas excluded here).
- No DSE runs after the lowering pipeline, so ends cannot cause store elimination
  behind our back (and any store made dead by an end is genuinely dead anyway).

## Validation plan

- lit tests: straight-line merge, loop body, fan-out-in-loop, multi-exit region
  (2 ends, conservative-but-exact), unreachable-read (cold-path subsumption),
  multi-region bail, escape bails, existing-start-not-dominating bail.
- Acceptance on gcframe-wip/shapes.jl: straight_16 352→~150 B, loop_fanout_16
  336→~160 B, pairs_16 608→~250 B; ef2 expected ~1,072→~1,030 B (residual
  UnitRanges), litmus unchanged or better.
- Full ladder: JuliaLowering suite, Base core, heap-hint stress, llvmpasses, clang
  static analysis, full bootstrap; sysimage build-time delta as compile-cost check.

## Effort and risk

Roughly three work units: pass + registration; lit tests; validation/tuning.
Dominant risk is misclassifying a reader/writer (attribute lies, partial-clobber
subtleties) — mitigated by the strict bail list, the single-def restriction, and
the fact that any bug manifests as slot-merge corruption, which the heap-hint
stress + suite ladder has caught reliably all campaign.
