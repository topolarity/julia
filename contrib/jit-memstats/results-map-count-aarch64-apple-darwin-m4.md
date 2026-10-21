<!-- Produced from the logs of `contrib/jit-memstats/map_count.jl 40000`, run once per mode
     (concurrently) with `nice -n 10`. -->

# Memory mappings per JIT graph (`map_count.jl`)

- machine: `arm64-apple-darwin25.5.0` (Apple M4), page size 16384 bytes
- `split` and `arena` use `ProtectAllocator`; mappings are the entries of the task's VM map (the dyld shared cache counts as a few submap entries)
- exit status: `split status=0 elapsed=252s`, `arena status=0 elapsed=252s`, `mapper status=0 elapsed=253s`

| functions | graphs | mappings split | mappings arena | mappings mapper | RSS MiB split | RSS MiB arena | RSS MiB mapper |
|---|---|---|---|---|---|---|---|
| 0 | 5 | 157 | 165 | 163 | 177 | 177 | 177 |
| 1000 | 1008 | 161 | 169 | 2172 | 257 | 258 | 274 |
| 2000 | 2008 | 167 | 175 | 4172 | 293 | 293 | 325 |
| 4000 | 4008 | 176 | 184 | 8173 | 363 | 370 | 425 |
| 8000 | 8008 | 195 | 202 | 16179 | 619 | 621 | 746 |
| 12000 | 12008 | 214 | 221 | 24182 | 720 | 721 | 909 |
| 16000 | 16008 | 232 | 238 | 32185 | 812 | 812 | 1065 |
| 20000 | 20008 | 253 | 260 | 40189 | 908 | 907 | 1224 |
| 24000 | 24008 | 271 | 277 | 48193 | 994 | 992 | 1372 |
| 28000 | 28008 | 291 | 296 | 56200 | 1079 | 1077 | 1525 |
| 32000 | 32008 | 309 | 315 | 64202 | 1162 | 1159 | 1670 |
| 36000 | 36008 | 328 | 331 | 72205 | 1249 | 1247 | 1820 |
| 40000 | 40008 | 346 | 350 | 80208 | 1339 | 1337 | 1972 |

`mapper` adds 2 mappings per graph, as on Linux, but did not fail at 80k
mappings: macOS has no limit like Linux's `vm.max_map_count` at this scale.
The arena run used a single arena throughout.

Absolute RSS on macOS varies a lot between runs (memory compression and the
load from other processes): a later run of the same workload measured 905 MiB
at 4000 functions in both `split` and `arena`. Compare RSS only between modes
run side by side; the JIT's own mapped memory is stable across runs.

With 256 MiB arenas (64 blocks of 16 KiB pages), the same workload switches
arenas twice by 40000 functions; run side by side with `split`:

| functions | arenas | mappings split / arena | RSS MiB split / arena | JIT mapped MiB split / arena |
|---|---|---|---|---|
| 16000 | 1 | 231 / 231 | 1342 / 1342 | 256 / 256 |
| 24000 | 2 | 270 / 272 | 1555 / 1557 | 380 / 381 |
| 40000 | 3 | 345 / 347 | 1948 / 1948 | 632 / 635 |
