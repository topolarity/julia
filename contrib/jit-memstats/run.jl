# Usage: julia contrib/jit-memstats/run.jl [reps]
#
# Runs each workload `reps` times (default 5) under each JULIA_JIT_MM mode,
# interleaving the modes, and prints a Markdown summary.
using Printf, Statistics

const DIR = @__DIR__
const REPS = isempty(ARGS) ? 5 : parse(Int, ARGS[1])
const MODES = ["split", "arena", "mapper"]
const WORKLOADS = ["many_small.jl", "realistic.jl"]

function run_one(mode, workload)
    cmd = addenv(`$(Base.julia_cmd()) --startup-file=no $(joinpath(DIR, workload))`,
                 "JULIA_JIT_MM" => mode)
    out = IOBuffer()
    ok = success(pipeline(cmd; stdout=out, stderr=out))
    s = String(take!(out))
    line = findfirst(l -> startswith(l, "RESULT "), split(s, '\n'))
    if !ok || line === nothing
        return Dict{String,String}("mode" => mode, "failed" => "true",
                                   "output" => last(s, 2000))
    end
    kv = Dict{String,String}()
    for f in split(split(s, '\n')[line])[2:end]
        k, v = split(f, '='; limit=2)
        kv[k] = v
    end
    return kv
end

mib(x) = @sprintf("%.2f", x / 2^20)

println("# JIT memory measurement\n")
println("- machine: `", Sys.MACHINE, "`, CPU: `", Sys.cpu_info()[1].model, "`")
println("- page size: ", ccall(:jl_getpagesize, Clong, ()), " bytes")
println("- julia: `", Base.GIT_VERSION_INFO.commit_short, "` (", Base.GIT_VERSION_INFO.branch, ")")
println("- reps per mode: ", REPS, " (modes interleaved)\n")

for w in WORKLOADS
    results = Dict(m => Dict{String,String}[] for m in MODES)
    for r in 1:REPS, m in MODES
        push!(results[m], run_one(m, w))
    end
    println("## ", w, "\n")
    println("| mode | allocator | graphs | content MiB | mapped MiB | wr buf MiB | per-graph pages 4k / 16k / 64k MiB | arenas | RSS MiB median (min–max) |")
    println("|---|---|---|---|---|---|---|---|---|")
    for m in MODES
        rs = results[m]
        bad = filter(r -> haskey(r, "failed"), rs)
        if !isempty(bad)
            println("| $m | FAILED ($(length(bad))/$(length(rs))) | | | | | | | |")
            println(stderr, "--- $w / $m failure output ---\n", bad[1]["output"])
            filter!(r -> !haskey(r, "failed"), rs)
            isempty(rs) && continue
        end
        g(k) = median([parse(Float64, r[k]) for r in rs])
        rss = [parse(Float64, r["rss"]) for r in rs]
        mapped = rs[1]["allocator"] == "mapper" ? "—" : mib(g("mapped"))
        wrbuf = rs[1]["allocator"] == "mapper" ? "—" : mib(g("wrbuf"))
        @printf("| %s | %s | %d | %s | %s | %s | %s / %s / %s | %d | %s (%s–%s) |\n",
                m, rs[1]["allocator"], g("graphs"), mib(g("content")), mapped, wrbuf,
                mib(g("pp4k")), mib(g("pp16k")), mib(g("pp64k")), g("arenas"),
                mib(median(rss)), mib(minimum(rss)), mib(maximum(rss)))
    end
    println()
end
