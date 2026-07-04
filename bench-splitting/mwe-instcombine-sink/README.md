# Standalone repro: InstCombine equal-frequency sinking pessimization

Minimal demonstration for the LLVM patch
"[InstCombine] Do not sink instructions across equal-frequency edges"
(~/repos/llvm-project branch instcombine-sink-colder-blocks).

## The kernel (gen_kernel.py, ~40 lines)

8-lane batched polynomial-chain evaluation (the multi-accumulator /
Estrin-style ILP pattern), written interleaved as any performance-aware
source is, with three structural features:

1. a straight seam (`br label %stage2call`) before the combining call —
   as left by block-partitioning passes (e.g. Julia's function splitter);
2. a call consuming the 8 chain results (a pipeline stage boundary);
3. a short continuation after the call reusing the same coefficients.

## The mechanism (pass-by-pass provenance + greedy trace + kill-switch A/Bs)

Established with -print-after dumps, -debug-only=regalloc traces on a
minimal N=200(rescued)/N=400(welded) pair, and causal flag flips.
(This section replaces an earlier account; see Retractions below.)

1. Stock InstCombine's sink cascade reassembles the 8 chains contiguously
   across the seam (grouped: 8 runs of 1600 dependent FMAs, in reverse
   emission order, with the chain-head fadds sunk adjacent to each chain).
2. The pre-RA machine scheduler is order-preserving: MIR after
   machine-scheduler and after virtregrewriter is still fully grouped in
   BOTH the welded and rescued cases.
3. The ONLY re-interleaver is the post-RA list scheduler
   (PostRASchedulerList: Znver4Model sets PostRAScheduler=1;
   MISchedPostRA defaults off). Kill-switch: -post-RA-scheduler=0 on an
   un-welded build leaves the final asm grouped (8x1600 runs, 13051
   ns/call vs 1700 with it). It schedules within the dependency DAG and
   cannot rename: X86's ANTIDEP_CRITICAL CriticalAntiDepBreaker excludes
   tied operands (KeepRegs via isRegTiedToUseOperand) — FMA accumulators
   are tied — and attacks one edge per critical-path step only.
4. The scale-dependent trigger is the RegisterCoalescer's large-interval
   throttle (RegisterCoalescer.cpp: LargeIntervalSizeThreshold=100
   valnos, LargeIntervalFreqThreshold=100 joins): long grouped chains
   (one vreg redefined per FMA) exceed it and stop coalescing, so each
   chain reaches greedy fragmented into multiple vregs (visible in the
   trace: two+ vregs per chain at N=400, one at N=200 — matching the
   weld onset between those sizes). CAUSAL CONFIRMATION: raising both
   thresholds un-welds every case including the original sunk module —
   run-length 1, 8 distinct regs, 10432 -> 1700 ns/call, exactly the
   patched-InstCombine reference (1702). Cost: llc time 0.71s -> 1.50s
   on this function (the throttle guards quadratic coalescing).
5. How fragmentation becomes serialization — the exact lock, read off
   the post-RA scheduler's own dependency DAG (-debug-only=post-RA-sched,
   d400 welded vs dr400 rescued): the chain FMA bodies are mutually
   hazard-free in BOTH cases; the weld is carried entirely by the CHAIN
   HEADS. Constants that lose their whole-range homes (the coalescer
   commute-merges some addends into the post-call tail chains; those
   intervals overlap the call's regmask — no callee-saved XMM, so all 32
   regs are blocked for any call-covering interval — and local-splitting
   produces short per-region pieces) get first-fit assigned to the
   LOWEST free register in each region. With sunk chain heads, the
   lowest free registers during early regions are precisely the LATER
   chains' accumulator registers (those chains haven't started). The
   next chain's head — the first redefinition of that register — then
   carries Anti edges to the previous region's constant reads, which
   extend to the region's end (e.g. SU(412) chain-6 head Anti<-SU(406)
   chain-7 tail; the boundary copy $xmm1 = VMOVAPS $xmm6 moving the
   constant out is visible in the DAG). Head-of-chain-k waits on
   tail-of-chain-k+1, one link per region: full serialization.
   In the rescued layout the heads (and constant homes) are all defined
   at region top, the accumulator registers are occupied by their own
   chains from cycle 0, constants live stably in xmm8-15, no such edges
   exist, and the latency-priority queue round-robins all 8 chains.
   NOTE: fit is not the issue, placement is — in the welded sunk-heads
   variant with only 6 addends, xmm8-15 has free slots (census 8) and
   xmm16-31 is always free, yet first-fit still parks constants in the
   future accumulator registers and the weld persists. Conversely,
   entry-heads with 8 addends (census 9) also welds. Head placement
   alone (= whether accumulator regs are exposed to first-fit parking)
   is the discriminator between the minimal pair.
6. xmm16-31 non-use, resolved: the FR64X allocation order does contain
   all 32 registers (greedy log). Intervals overlapping the regmask can
   be assigned NO register (mask blocks all 32 equally); mask-free
   pieces are small and first-fit lands in the low half. A no-call
   18-chain variant does use xmm16-25. No cost heuristic involved
   (all XMM CostPerUse=0).

Sensitivity (why naive repros kept getting rescued): outcome flips on
razor-thin structural details — chain emission order (forward welds 1
chain at N>=400, reverse welds 0 with entry-placed heads and 4-6 with
sunk heads) and chain-head placement. Single-variable conclusions from
one kernel shape are unreliable; the coalescer-throttle A/B is the only
variable that flips the outcome cleanly in both directions.

Retractions of the earlier account (measurement artifacts): the pre-RA
scheduler does NOT chunk into ~355-op runs (asm-comment parsing bug);
RA does NOT weld all chain runs onto one register under "hot-value
pressure" (at N=400 every chain piece got its hinted register; the
serialization enters via the constants' split pieces); "never touches
xmm16-31" was checked only on the welded build ($xmm vs %xmm parse bug).

## Reproduce

    python3 gen_kernel.py                     # MN=1600 SCRATCH=. -> mwe_final.ll
    opt-stock   -passes=instcombine mwe_final.ll -S -o stock.ll
    opt-patched -passes=instcombine mwe_final.ll -S -o patched.ll
    llc -O2 -mcpu=znver4 {stock,patched}.ll ; gcc -O2 driver.c ...

## Measured (Zen 4 / EPYC 9354, LLVM 21.1.8 base)

    stock   InstCombine: 10433 ns/call   0.816 ns/step
    patched InstCombine:  1702 ns/call   0.133 ns/step   (6.1x)

Onset vs chain length N (grouped-vs-interleaved, direct generation):
N=200 no delta (OOO absorbs); N=400 1.8x; N=800 1.9x; N=1600 6.1x.

Identical output sums in all configurations.
