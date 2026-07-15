# MWE: super-linear backend on a giant block of calls with values live across

Shape 2 (dynamic-dispatch-heavy code): one huge block of N calls, each
producing a value that stays live across the remaining safepoints. This is the
"rooted values live across calls" pattern.

## Reproduce

    python3 gen.py 4000    > q.ll        # one huge block
    python3 gen.py 4000 64 > qc.ll       # br every 64 calls
    llc -O2 -mcpu=native -time-passes q.ll -o /dev/null

## Measured (llc -time-passes, N=2000 -> 4000, this build)

    GreedyRegisterAllocator   0.075 -> 0.277s   (~3.6x per 2x = super-linear)
    Post-RA list scheduler    1.85  -> 4.39s
    MachineInstructionSched   0.47  -> 1.05s
    Total                     2.43  -> 5.95s

A giant block drives several backend passes super-linear at once; GreedyRA is
super-linear in the values live across the block's safepoints.

## The lever is FUNCTION-splitting, not block-splitting

Chunking the block with unconditional branches (`gen.py N 64`) does NOT help
(RA 0.277 -> 0.326s, Total 5.95 -> 6.15s): the values are live across the whole
block, and inserting block boundaries keeps them live in registers across those
boundaries, so RA still sees every live range. Only region OUTLINING breaks the
spans -- the splitter marshals values through memory at region boundaries, so
each outlined function's RA sees only the values live within it. This is why
the F/B study finds GreedyRA is an F-lever (function-split) win, not a B-lever
(block-split) win, on call-dense code (both giant-block B=0 and small-block
B=40 regimes). The block/region safepoint budgets bound RA by sizing the
outlined regions, not by mere block cutting.
