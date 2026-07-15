# mwe-gvn-storewall — isolated GVN superlinearity (reversediff reduction)

Reproduces, under bare `opt -passes=gvn`, the GVN pathology that dominates
tracked-ReverseDiff compile (GVN ~77s of ~100s at N=8). Redundant load-forwarding
across a branchy CFG: each load is forwarded to an earlier store, and each forward
dirties the MemDep non-local cache, so re-walks compound.

## Generators
- `gen.py` == `gen6.py` (CANONICAL, pointer-phi): the load CURSOR is phi'd through
  each diamond, so the load pointer arrives via a phi and MemDep must PHI-translate
  it (PHITransAddr) across both arms — the reversediff mechanism (tracked values flow
  through branches as pointer identities). Args `N BS` (units, units/block).
  ~34 NoAlias/load at BS=1 (vs 2 for the const-ptr version), toward reversediff's ~850.
- `gen2.py` (const-ptr): loads a constant `base[0]`; superlinear via cache invalidation
  but weak branchy term (2 NoAlias/load). Kept as the minimal reproducer.
- `gen3/4/5.py`: discriminators (below).

## Resolved cost model (bare opt, LLVM 21, ~/repos/llvm-project/build-sink/bin/opt)
GVN cost = **a·insts** (value-numbering, linear) + **b·insts·blocks** (branchy
PHI-translated non-local memdep walk). Evidence:
- gen3 (vary RAW blocks via UNCONDITIONAL splits, fixed insts): FLAT — unconditional
  chains are cacheable single-pred, no walk. Raw block count is NOT a driver.
- gen4 (vary branchiness/diamonds): GVN RISES while NoAlias FALLS — cost is the
  PHI-translated multi-pred walk, not alias-query count.
- gen5 (fixed blocks, vary insts via padding): LINEAR — value-numbering term.
- fixed BLOCK COUNT, grow N: ~linear (exp ~1.15) => rules out insts^2.
- fixed block SIZE (blocks ∝ N): superlinear (exp 1.3-1.9). Large blocks (BS=256)
  12x cheaper than BS=1 at N=16000 (fewer branchy boundaries).
=> superlinear term is **insts × (branchy) blocks**, NOT insts^2.

## Mechanism (Cody)
To find a load's definition GVN proves NoAlias vs every intervening store (any MayAlias
stops the forward); a store to an unaliased ptr in a DOMINATOR is a strong update that
ceases the pred walk. Branchiness (diamonds/phis) creates MayAlias relationships + new
pointer identities to track, and defeats dominator short-circuiting -> long walls.

## Tuning takeaway
Since cost ~ insts·blocks and blocks <= insts, bounding INSTRUCTIONS per region caps
per-region cost <= R^2 => instruction-based region-size already bounds it. A
blocks-per-region cap would be more precise but is not necessary.
