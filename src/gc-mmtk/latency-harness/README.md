# ConcurrentImmix latency harnesses

Benchmarks/gates used during the 2026-07/08 concurrent-sweep + pause-latency
campaign. All take the iteration count as ARGS[1] and print one summary line.

- `val.jl`   - correctness gate (checksum) + pause stats, single mutator
- `mt.jl`    - 8-thread correctness gate + per-thread worst-stall stats
- `tail.jl`  - per-pause-kind mean/max attribution (Init/Final/Full)
- `tailp.jl` - tail.jl + in-pause slow-packet + pause-anatomy reporting
- `tailm.jl` - tailp.jl + mutator-side stall stats (jl_gc_mutator_stall_*)
- `tailh.jl` - iteration-stall histogram (no rusage)
- `tailr.jl` - per-stall getrusage attribution (faults/ctx-switches/stime)
- `spin.jl`  - GC-free spin-loop control for machine-noise floor

Run pattern (heap limit in GB; use numactl, NOT bare taskset -- kernel NUMA
balancing otherwise injects multi-ms stalls into large-RSS mutators):

    env MMTK_MIN_HSIZE_G=8 MMTK_MAX_HSIZE_G=8 \
      numactl --physcpubind=<node cpus> --membind=<node> \
      ./julia --startup-file=no --gcthreads=16 tailm.jl 300000000
