# JIT memory measurement

- machine: `x86_64-linux-gnu`, CPU: `AMD EPYC 9354 32-Core Processor`
- page size: 4096 bytes
- julia: `a969df8001*` (ct/tmp-jit-memstats)
- reps per mode: 5 (modes interleaved)

## many_small.jl

| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |
|---|---|---|---|---|---|---|---|---|
| split | selfmem | 3004 | 0.58 | 3.00 | 2.00 | 23.47 / 93.89 / 375.56 | 0 | 286.00 (286.00–287.00) |
| arena | selfmem | 3004 | 0.58 | 3.00 | 2.00 | 23.47 / 93.89 / 375.56 | 1 | 286.00 (286.00–286.00) |
| mapper | mapper | 3004 | 0.58 | — | — | 23.47 / 93.89 / 375.56 | 0 | 311.00 (310.00–311.00) |

## realistic.jl

| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |
|---|---|---|---|---|---|---|---|---|
| split | selfmem | 1690 | 3.63 | 5.85 | 2.00 | 16.34 / 58.45 / 229.31 | 0 | 520.12 (519.05–540.75) |
| arena | selfmem | 1690 | 3.63 | 5.85 | 2.00 | 16.34 / 58.45 / 229.31 | 1 | 519.62 (518.38–544.52) |
| mapper | mapper | 1690 | 3.63 | — | — | 16.34 / 58.45 / 229.31 | 0 | 533.25 (532.05–534.55) |
