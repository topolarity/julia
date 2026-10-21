# Usage: julia contrib/jit-memstats/compare_60915.jl <julia with this branch> <julia with #60915> [reps]
#
# Compares the memory managers of this branch (each JULIA_JIT_MM mode) and of
# JuliaLang/julia#60915 (its dual-mapped allocator and its fallback to
# MapperJITLinkMemoryManager) on the workloads in this directory, using only
# what common.jl can measure on both builds: RSS and the number of mappings.
# The object cache is disabled so that every run generates its own code.
#
# For a like-for-like comparison, build #60915's libjulia-codegen and swap it
# into a copy of this branch's `usr/` (its changes are all in libjulia-codegen),
# with a `test` symlink next to that `usr/` for realistic.jl.
using Printf, Statistics

const DIR = @__DIR__
const OURS, PR = ARGS[1], ARGS[2]
const REPS = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 5
const CONFIGS = [
    ("branch split",    OURS, ["JULIA_JIT_MM" => "split"]),
    ("branch arena",    OURS, ["JULIA_JIT_MM" => "arena"]),
    ("branch mapper",   OURS, ["JULIA_JIT_MM" => "mapper"]),
    ("#60915 dual",     PR,   ["JULIA_CGMEMMGR_MAP_TYPE" => "dual"]),
    ("#60915 fallback", PR,   ["JULIA_CGMEMMGR_MAP_TYPE" => "fallback"]),
]
const WORKLOADS = ["many_small.jl", "realistic.jl", "far_placement.jl"]

function run_one(exe, env, workload)
    cmd = addenv(`$exe --startup-file=no $(joinpath(DIR, workload))`,
                 "JULIA_OBJCACHE" => "0", env...)
    out = IOBuffer()
    ok = success(pipeline(cmd; stdout=out, stderr=out))
    s = String(take!(out))
    i = findlast(l -> startswith(l, "RESULT "), split(s, '\n'))
    (ok && i !== nothing) || return (; failed=true, output=last(s, 1500))
    kv = Dict(split(f, '='; limit=2)[1] => split(f, '='; limit=2)[2]
              for f in split(split(s, '\n')[i])[2:end])
    return (; failed=false, allocator=kv["allocator"], rss=parse(Float64, kv["rss"]) / 2^20,
            mappings=parse(Int, kv["mappings"]))
end

println("# JIT memory managers: this branch vs JuliaLang/julia#60915\n")
println("- machine: `", Sys.MACHINE, "`, CPU: `", Sys.cpu_info()[1].model, "`, page size: ",
        ccall(:jl_getpagesize, Clong, ()), " bytes")
println("- `JULIA_OBJCACHE=0`; ", REPS, " reps per configuration, interleaved\n")
for w in WORKLOADS
    res = Dict(c[1] => [] for c in CONFIGS)
    for _ in 1:REPS, (name, exe, env) in CONFIGS
        push!(res[name], run_one(exe, env, w))
    end
    println("## ", w, "\n")
    println("| configuration | allocator | ok | RSS MiB median (min–max) | mappings median |")
    println("|---|---|---|---|---|")
    for (name, _, _) in CONFIGS
        rs = res[name]
        good = filter(r -> !r.failed, rs)
        if isempty(good)
            println("| $name | | 0/$(length(rs)) | | |")
        else
            rss = [r.rss for r in good]
            @printf("| %s | %s | %d/%d | %.1f (%.1f–%.1f) | %d |\n", name, good[1].allocator,
                    length(good), length(rs), median(rss), minimum(rss), maximum(rss),
                    median([r.mappings for r in good]))
        end
        bad = filter(r -> r.failed, rs)
        isempty(bad) || println(stderr, "--- $w / $name failure ---\n", bad[1].output)
    end
    println()
end
