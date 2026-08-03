# Generational campaign baselines (pre-nursery tip bbfaa83d80 + Phase 0 scaffolding)

All runs: `numactl --physcpubind=96-127 --membind=1`, `--gcthreads=16`,
`JULIA_NUM_THREADS=1` unless noted. Default heap config unless noted.
Recorded 2026-08-03 on the Zen4 dev box.

## passes.jl 30M (steady-state wall, passes 2-4)

| Config | wall (s) | stw | triage | block |
|---|---|---|---|---|
| default (2 reps) | 1.65-1.86 | 3.0-3.7ms | 66-79ms | 0 |
| 8G | 1.69-1.77 | 2.8-2.9ms | 66-73ms | 0 |

Pass 1 (warmup/first-touch): 2.0-2.2s.

## tailm.jl 10M (latency)

| Config | tmax | Init mean/max | Final mean/max | Full | mstall max |
|---|---|---|---|---|---|
| default | 0.4ms | 0.04/0.06ms | 0.13/0.22ms | - | 0.22ms |
| hard-cap 320MB | 1.2ms | 0.06/0.07ms | 0.14/0.19ms | - | 0.23ms |

block_max=0 in both.

## trigger-churn.jl (default config, 10M iters)

wall 0.96s, cycles 8, full 0, concurrent 8, minor 0.

## val.jl 10M / mt.jl 8x3M

val: sum correct, tmax 0.4ms, 25 cycles, stw/cycle 0.07ms.
mt: sums correct on all 8 threads, per-cycle stw 1.07ms (worst thread),
tmax 17ms (thread max; MT pause tail is a known pre-existing gap).

## Cross-collector reference (same box, measured this campaign)

| Collector | passes wall | mutator IPC | fills/G-instr (mutator) |
|---|---|---|---|
| stock (wt-wb-ab) | 0.92-0.98s | 4.58 | L2-resident: 210M L2, 11.8M DRAM total |
| StickyImmix (GC tree) | 1.19-1.30s | 3.67 | L3-tier: 1.65M L3 + 1.71M DRAM |
| ConcurrentImmix (this) | 1.65-2.0s | 2.51 | DRAM-tier: 2.67M DRAM, 0.16M L3 |

Acceptance targets for the generational work are in GENERATIONAL-PLAN.md
section 1 (wall <= 1.35s, IPC >= 3.3, minor p99 <= 0.5ms, majors unchanged,
zero blocking, gates green).
