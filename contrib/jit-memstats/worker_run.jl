# Usage: julia contrib/jit-memstats/worker_run.jl [testname...]
#
# Runs the same sequence of test files in one process per JULIA_JIT_MM mode
# (the modes run concurrently), with the test workers' flags, and prints how
# the number of graphs and of memory mappings grows after each test.
using Printf
const DIR = @__DIR__
const TESTDIR = joinpath(Sys.BINDIR, "..", "..", "test")
cd(() -> include(joinpath(TESTDIR, "testenv.jl")), TESTDIR)
const MODES = ["split", "arena", "mapper"]
const TESTS = isempty(ARGS) ? [
    "dict", "strings/basic", "strings/search", "strings/util", "tuple",
    "iterators", "reduce", "intfuncs", "rational", "bitarray", "copy",
    "functional", "operators", "ordering", "sets", "missing", "namedtuple",
    "char", "hashing", "iobuffer", "enums", "abstractarray",
] : ARGS

parse_result(l) = Dict(split(f, '='; limit=2)[1] => split(f, '='; limit=2)[2] for f in split(l)[2:end])

results = Dict{String,Vector{Dict{String,SubString{String}}}}()
failures = Dict{String,String}()
@sync for m in MODES
    @async begin
        cmd = addenv(`$test_exename $test_exeflags $(joinpath(DIR, "worker.jl")) $TESTS`,
                     "JULIA_JIT_MM" => m)
        out = IOBuffer(); err = IOBuffer()
        ok = success(pipeline(cmd; stdout=out, stderr=err))
        lines = filter(l -> startswith(l, "RESULT "), split(String(take!(out)), '\n'))
        results[m] = parse_result.(lines)
        e = String(take!(err))
        ok || (failures[m] = last(e, 3000))
        errs = filter(l -> startswith(l, "test error"), split(e, '\n'))
        isempty(errs) || println(stderr, "$m: ", join(errs, "\n$m: "))
    end
end

println("# Test-worker emulation: JIT graphs and memory mappings\n")
println("- machine: `", Sys.MACHINE, "`, page size: ", ccall(:jl_getpagesize, Clong, ()), " bytes")
Sys.islinux() && println("- `vm.max_map_count`: ", strip(read("/proc/sys/vm/max_map_count", String)))
println("- one process per mode, test workers' flags: `", join(test_exeflags.exec, ' '), "`\n")
println("| after test | graphs | ", join(("mappings $m" for m in MODES), " | "), " | ",
        join(("RSS MiB $m" for m in MODES), " | "), " |")
println("|---|---|", repeat("---|", 2 * length(MODES)))
for (i, t) in enumerate(TESTS)
    row = [get(get(results[m], i, Dict()), "mappings", "—") for m in MODES]
    rss = [haskey(get(results[m], i, Dict()), "rss") ?
           @sprintf("%.0f", parse(Float64, results[m][i]["rss"]) / 2^20) : "—" for m in MODES]
    g = get(get(results["split"], i, Dict()), "graphs", "—")
    println("| $t | $g | ", join(row, " | "), " | ", join(rss, " | "), " |")
end
for (m, e) in failures
    println("\n`$m` exited with an error; end of its stderr:\n\n```\n", e, "\n```")
end
