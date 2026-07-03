# Normalize perf_matrix.sh output into per-iteration and per-boundary rates
# (see PERF.md).
#
#   julia perf_analyze.jl perfout/
#
# For each perf_<S>_<CH>.txt: parse the perf-stat windows and PERFDONE,
# convert each counter to events/sec using its own window's elapsed time, then
#   per_iter(X)     = X/sec / (iters/sec)
#   per_boundary(X) = (per_iter(X)_split - per_iter(X)_off) / boundaries
# cycles are normalized per window; iters/sec comes from the whole loop
# (steady-state assumption; single fixed hot function).
using Printf

# realized region counts (boundaries ~= leaf regions; verified 2026-07-03 via
# -julia-split-time on this tree: 256k -> 356/183/93/47 for c1600/3200/6400/12800)
const BOUNDARIES = Dict(
    (64000, "400") => 324, (64000, "1600") => 81,
    (256000, "400") => 1284, (256000, "1600") => 356,
    (256000, "3200") => 183, (256000, "6400") => 93, (256000, "12800") => 47)

struct Run
    iters_per_sec::Float64
    ev::Dict{String,Float64}   # events/sec
end

function parse_run(path)
    txt = read(path, String)
    m = match(r"PERFDONE iters=(\d+) secs=([\d.]+)", txt)
    m === nothing && return nothing
    ips = parse(Int, m.captures[1]) / parse(Float64, m.captures[2])
    ev = Dict{String,Float64}()
    for grp in split(txt, r"### GROUP=")[2:end]
        el = match(r"([\d.]+) seconds time elapsed", grp)
        el === nothing && continue
        secs = parse(Float64, el.captures[1])
        for line in eachmatch(r"^\s+([\d,]+)\s+([A-Za-z][\w.-]+)\s*(?:#.*)?$"m, grp)
            cnt = parse(Float64, replace(line.captures[1], "," => ""))
            name = line.captures[2]
            name in ("cycles", "instructions") && haskey(ev, name) && continue
            ev[name] = get(ev, name, 0.0) == 0.0 ? cnt / secs : ev[name]
        end
    end
    Run(ips, ev)
end

dir = ARGS[1]
runs = Dict{Tuple{Int,String},Run}()
for f in readdir(dir; join=true)
    m = match(r"perf_(\d+)_(\w+)\.txt", basename(f))
    m === nothing && continue
    r = parse_run(f)
    r === nothing && (println("SKIP (no PERFDONE): ", f); continue)
    runs[(parse(Int, m.captures[1]), m.captures[2])] = r
end

evnames = sort(collect(union((keys(r.ev) for r in values(runs))...)))
chnum(c) = something(tryparse(Int, c), typemax(Int))
for S in sort(unique(first.(collect(keys(runs)))))
    haskey(runs, (S, "off")) || continue
    off = runs[(S, "off")]
    chs = sort([c for (s, c) in keys(runs) if s == S && c != "off"]; by=chnum)
    @printf("\n== S=%d ==  (off: %.0f iters/s, %.2f us/iter)\n", S, off.iters_per_sec, 1e6 / off.iters_per_sec)
    @printf("%-45s %12s", "event (per iter)", "off")
    for CH in chs
        @printf(" %12s", "c$CH")
    end
    println()
    for name in evnames
        haskey(off.ev, name) || continue
        @printf("%-45s %12.1f", name, off.ev[name] / off.iters_per_sec)
        for CH in chs
            r = runs[(S, CH)]
            haskey(r.ev, name) ? @printf(" %12.1f", r.ev[name] / r.iters_per_sec) : @printf(" %12s", "-")
        end
        println()
    end
    for CH in chs
        r = runs[(S, CH)]
        us = 1e6 / r.iters_per_sec
        dus = us - 1e6 / off.iters_per_sec
        if haskey(BOUNDARIES, (S, CH))
            b = BOUNDARIES[(S, CH)]
            @printf("c%-6s %8.2f us/iter  penalty %+7.2f us  (%d boundaries -> %+6.1f ns/boundary)\n",
                    CH, us, dus, b, dus * 1000 / b)
        else
            @printf("c%-6s %8.2f us/iter  penalty %+7.2f us\n", CH, us, dus)
        end
    end
end
