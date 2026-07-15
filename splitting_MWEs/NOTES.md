# Maintainer notes: function-splitting tuning campaign (2026-07)

Distilled experimental record for whoever tunes or extends
`llvm-function-splitting.cpp` next. See README.md for the MWE inventory and
observed per-pass scaling.

## Methodology that worked (and mistakes to avoid)

- **Tune one axis at a time**: (1) measure the *intrinsic* compile curve by
  growing the unsplit quantity (block size / function size / safepoint count)
  and find where it leaves linear; (2) set the threshold at the largest still-
  linear size; (3) validate by re-sweeping the workload size and confirming
  the curve linearizes. Never 2D-scan threshold-vs-size.
- **Disable passes entirely to exclude them** (dedicated
  `BasicBlockSplittingPass` vs builtin `FunctionSplittingPass` toggles); never
  reason about pass-internal gates. Setting `block-threshold` with the builtin
  pass on still outlines (BigBlocks qualifies the function).
- **Keep safepoint budgets proportional to their size knob** in isolation
  runs, or they silently outline and confound the lever.
- **Call-free shapes cannot ground call/safepoint conclusions.** Twice this
  campaign a "knob X is irrelevant" result was vacuous because the shapes that
  exercise X were missing from the sweep.
- Best-of-N timing on a shared box; noise is upward. Prefer causal A/B (kill
  switch or single-flag flip) over correlation.
- `-julia-split-time` prints per-function region formation:
  `cuts(target/sp/blocks/clamp)` + `growfail(blocks/size/stuck)` — use it to
  verify WHICH cap actually binds before interpreting any sweep.
- `-stats` (LLVM statistics) works in the assertions build and was decisive
  for the GVN mechanism (NoAlias counts, uncached non-local memdep queries).

## Cost models behind the caps

- **GVN** = linear(insts) + superlinear(insts x branchy blocks). The costly
  work is the PHI-translated non-local memdep walk; to forward a load past a
  store wall it must prove NoAlias against every intervening store, and a
  store to an unaliased pointer in a dominator is a strong update that stops
  the walk. Diamonds/pointer-phis create new pointer identities that defeat
  both caching and dominator short-circuiting. Hence `region-blocks`.
- **GreedyRA/MachineCSE** superlinear in rooted live ranges across safepoints
  per function; block cuts do NOT help (SSA values stay live across block
  boundaries) — only outlining (marshalling through memory) breaks ranges.
  Hence `region-safepoints`.
- **SLP/ISel/early-InstCombine** superlinear in single-block size. Hence
  block chunking (`block-insts`), which is runtime-free.
- Region compile cost is a function of realized region SIZE, independent of
  which cap produced the cut.

## Key structural facts

- The maximal single-entry region from a seed is exactly the seed's DOMINATOR
  SUBTREE; the greedy Full-frontier growth converges to it (loop headers enter
  as retreating-edge debt). "Smarter growth" from a fixed seed cannot help.
  Dominator-guided seed ordering/filtering was implemented, measured to form
  byte-identical regions while costing MORE than the doomed micro-attempts it
  skipped (DomTree+weights+sort > tiny frontier scans), and deleted.
- Stuck-attempt size distribution is bimodal: thousands of ~10-inst glue
  shards (correctly abandoned) plus a fat tail of quarter-cap dense-CFG
  regions. The progress-fraction floor (>= 1/4 of any cap) rescues exactly
  the tail: -19..-24% compile on tracked ReverseDiff, no effect on shapes
  without it.
- Outlining is gated on exceeding a full cap; sub-cap functions stay whole
  (a whole-body extraction bounds nothing and pays interface + call).
- Boundary runtime tax falls ~1/region-size; +1-4% at the shipped defaults on
  the synthetic shapes. `arrays_store` documents the SLP schedule-budget
  toxic zone (~1.5-3k-inst regions) the defaults deliberately sit above.

## Refuted / dead ends (do not re-add without new evidence)

- Dominator-guided seeding (above).
- Software code-prefetch of the next region (`SplitPrefetchLines`) — no
  effect on the boundary tax.
- "Blocks-per-region is unnecessary because insts bounds blocks" — true only
  asymptotically; CFG density is the constant that matters (11 insts/block on
  tracked AD vs thousands on straight-line FP).
- Per-query cost / cache-thrash explanations of GVN superlinearity — the
  split A/B showed query COUNTS drop ~8.5x; it is walk length, not per-query
  cost.

## Open items

- `mwe-branchy-loop`: single loop bodies are unsplittable (no single-entry
  cut). Would need multi-entry extraction (entry-selector dispatch) or loop
  sub-region support.
- Unexplained `arrays_store` runtime reading at final defaults (0.305 vs
  0.137 ns/op under an older config); needs a controlled
  block-safepoints=128-vs-512 A/B before treating as a regression.
- Residual ~12% super-linearity in tracked ReverseDiff N=8->20 end-to-end
  (exponent ~1.12); non-LLVM share grows too, so possibly not pipeline; first
  suspects otherwise: caller residue + region callsite count (GroupSize
  hierarchy is the intended bound).
- InstCombine custom-LLVM commits vs mergeStraightSeams: see the A/B verdict
  appended to README.md (this campaign's item 3).
