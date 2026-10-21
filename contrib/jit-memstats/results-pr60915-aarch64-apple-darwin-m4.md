<!-- Produced with `contrib/jit-memstats/compare_60915.jl <branch julia> <#60915 julia> 5`.
     The #60915 build is its libjulia-codegen (head ff76472fd9; all its changes are in that
     library) swapped into a copy of this branch's usr/, so both share one sysimage and
     libjulia-internal. This branch is at "jit-memstats: drop ProtectAllocator", i.e. its split
     and arena modes use the dual-mapped allocator on macOS. -->

# JIT memory managers: this branch vs JuliaLang/julia#60915

- machine: `arm64-apple-darwin25.5.0`, CPU: `Apple M4`, page size: 16384 bytes
- `JULIA_OBJCACHE=0`; 5 reps per configuration, interleaved

## many_small.jl

| configuration | allocator | ok | RSS MiB median (min–max) | mappings median |
|---|---|---|---|---|
| branch split | dualmap | 5/5 | 248.5 (248.4–248.5) | 151 |
| branch arena | dualmap | 5/5 | 248.5 (248.5–248.7) | 153 |
| branch mapper | mapper | 5/5 | 342.6 (342.5–342.8) | 6165 |
| #60915 dual | uninstrumented | 5/5 | 248.0 (248.0–248.2) | 155 |
| #60915 fallback | uninstrumented | 5/5 | 342.2 (342.0–342.2) | 6167 |

## realistic.jl

| configuration | allocator | ok | RSS MiB median (min–max) | mappings median |
|---|---|---|---|---|
| branch split | dualmap | 5/5 | 601.8 (588.2–605.3) | 258 |
| branch arena | dualmap | 5/5 | 596.6 (587.0–601.0) | 258 |
| branch mapper | mapper | 5/5 | 646.7 (639.0–657.7) | 3639 |
| #60915 dual | uninstrumented | 5/5 | 597.7 (588.0–598.8) | 262 |
| #60915 fallback | uninstrumented | 5/5 | 649.3 (649.0–681.9) | 3641 |

## far_placement.jl

| configuration | allocator | ok | RSS MiB median (min–max) | mappings median |
|---|---|---|---|---|
| branch split | | 0/5 | | |
| branch arena | dualmap | 5/5 | 221.4 (221.4–221.5) | 13288 |
| branch mapper | mapper | 5/5 | 382.2 (382.1–382.3) | 13563 |
| #60915 dual | uninstrumented | 5/5 | 380.8 (380.7–380.9) | 13493 |
| #60915 fallback | uninstrumented | 5/5 | 381.5 (381.5–381.7) | 13544 |

In `far_placement.jl`, `branch split` fails on the first round with:

```
JIT session error: In graph far_big_1-jitted-9, section __TEXT,__text: relocation target 0x500100080 (_big) is out of range of Page21 fixup at address 0x500100080 (_julia_far_big_1_0u0, 0x114701748 + 0x0)
```

The RSS of `far_placement.jl` is dominated by its ten 16 MiB zero-initialized
globals: the mapper and #60915 zero-fill them explicitly, while the RW blocks of
this branch are fresh anonymous memory that is never touched. It is not a
measure of the memory managers.

## map_count.jl 40000 (run side by side, same reporting)

| functions | mappings split / arena / #60915 dual | RSS MiB split / arena / #60915 dual |
|---|---|---|
| 0 | 152 / 153 / 151 | 189 / 189 / 189 |
| 1000 | 152 / 154 / 152 | 239 / 239 / 240 |
| 4000 | 153 / 155 / 159 | 261 / 261 / 261 |
| 8000 | 157 / 159 / 169 | 280 / 280 / 280 |
| 16000 | 164 / 167 / 188 | 319 / 319 / 319 |
| 24000 | 173 / 175 / 210 | 362 / 362 / 362 |
| 32000 | 179 / 181 / 228 | 398 / 398 / 399 |
| 40000 | 185 / 187 / 246 | 445 / 444 / 445 |

## Before the dual-mapping probe fix

With `ProtectAllocator` (one sealed 16 KiB page per graph) instead of the
dual-mapped allocator, this branch's split and arena modes used more RSS than
#60915 by almost exactly one page per graph: 46 MiB on `many_small.jl` (3007
graphs), 28 MiB on `realistic.jl` (1691 graphs), and 617 MiB at 40000 functions
of `map_count.jl` (1062 vs 445 MiB).
