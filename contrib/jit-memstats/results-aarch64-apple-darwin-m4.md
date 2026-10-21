<!-- Measured with contrib/jit-memstats/run.jl 5 on 23b662007a plus the
     ProtectAllocator/far_placement commit; the version line below shows the
     commit the binary was built from (the harness change after it is
     Julia-only). On this machine "split" and "arena" use ProtectAllocator,
     which pads each segment to a page per finalization batch, so their
     memory numbers are not directly comparable to DualMapAllocator. -->

# JIT memory measurement

- machine: `arm64-apple-darwin25.5.0`, CPU: `Apple M4`
- page size: 16384 bytes
- julia: `7786edc67f*` (ct/tmp-jit-memstats)
- reps per mode: 5 (modes interleaved)

## many_small.jl

| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |
|---|---|---|---|---|---|---|---|---|
| split | protect | 3007 | 0.67 | 52.00 | 0.00 | 23.49 / 93.97 / 375.88 | 0 | 319.06 (318.83–319.20) |
| arena | protect | 3007 | 0.67 | 52.00 | 0.00 | 23.49 / 93.97 / 375.88 | 1 | 319.00 (318.83–319.08) |
| mapper | mapper | 3007 | 0.67 | — | — | 23.49 / 93.97 / 375.88 | 0 | 366.59 (366.31–366.70) |

## realistic.jl

| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |
|---|---|---|---|---|---|---|---|---|
| split | protect | 1691 | 3.08 | 32.00 | 0.00 | 14.64 / 53.66 / 211.69 | 0 | 537.09 (530.98–650.45) |
| arena | protect | 1691 | 3.08 | 32.00 | 0.00 | 14.64 / 53.66 / 211.69 | 1 | 537.66 (531.97–538.88) |
| mapper | mapper | 1691 | 3.08 | — | — | 14.64 / 53.66 / 211.69 | 0 | 562.81 (557.84–597.30) |

## far_placement.jl

| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |
|---|---|---|---|---|---|---|---|---|
| split | FAILED (5/5) | | | | | | | |
| arena | protect | 1513 | 0.93 | 28.00 | 0.00 | 11.82 / 47.28 / 189.12 | 1 | 302.39 (301.50–468.72) |
| mapper | mapper | 1513 | 0.93 | — | — | 11.82 / 47.28 / 189.12 | 0 | 327.03 (325.50–331.42) |


far_placement.jl / split: all 5 reps failed to link; output of the first:

```
JIT session error: In graph Unknown buffer, section __TEXT,__text: relocation target 0x1141b9638 (l_jlplt_ijl_cstr_to_string_0_got) is out of range of Page21 fixup at address 0x1141b9638 (l_jlplt_ijl_cstr_to_string_0, 0x16c091a06b8 + 0x44)
```
