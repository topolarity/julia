<!-- Produced from the logs of `contrib/jit-memstats/map_count.jl 40000`, run once per mode
     (concurrently) with `nice -n 10 numactl --cpunodebind=1 --membind=1`. -->

# Memory mappings per JIT graph (`map_count.jl`)

- machine: `x86_64-linux-gnu` (AMD EPYC 9354), page size 4096 bytes
- `vm.max_map_count`: 65530
- exit status: `split status=0 elapsed=419s`, `arena status=0 elapsed=419s`, `mapper status=134 elapsed=288s`

| functions | graphs | mappings split | mappings arena | mappings mapper | RSS MiB split | RSS MiB arena | RSS MiB mapper |
|---|---|---|---|---|---|---|---|
| 0 | 5 | 171 | 174 | 180 | 228 | 227 | 226 |
| 1000 | 1008 | 171 | 174 | 2186 | 295 | 296 | 302 |
| 2000 | 2008 | 171 | 174 | 4186 | 310 | 309 | 324 |
| 4000 | 4008 | 171 | 174 | 8187 | 329 | 329 | 359 |
| 8000 | 8008 | 173 | 176 | 16187 | 367 | 365 | 428 |
| 12000 | 12008 | 174 | 177 | 24189 | 411 | 408 | 502 |
| 16000 | 16008 | 176 | 179 | 32190 | 458 | 455 | 580 |
| 20000 | 20008 | 179 | 180 | 40190 | 511 | 507 | 664 |
| 24000 | 24008 | 181 | 182 | 48190 | 564 | 561 | 747 |
| 28000 | 28008 | 181 | 183 | 56191 | 616 | 609 | 832 |
| 32000 | 32008 | 182 | 184 | 64191 | 655 | 652 | 907 |
| 36000 | 36008 | 183 | 187 | — | 707 | 705 | — |
| 40000 | 40008 | 184 | 188 | — | 803 | 797 | — |

`mapper` stopped at function 32671; the first lines of its error output:

```
JIT session error: Cannot allocate memory
Internal error: Lookup failed: Failed to materialize symbols: { (JuliaOJIT, { jfptr_m_32671_0#0, julia_m_32671_0#0 }) }
```
