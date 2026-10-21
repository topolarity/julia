# Usage: julia contrib/jit-memstats/testsuite.jl <mode> <outfile.tsv> [ntasks] [tests...]
#
# Runs every default test (or the given ones) in its own process with
# JULIA_JIT_MM=<mode>, `ntasks` at a time, and writes one TSV row per test
# (each test's stderr goes to <outfile.tsv>.logs/).
const DIR = @__DIR__
const TESTDIR = joinpath(Sys.BINDIR, "..", "..", "test")
mode, outfile = ARGS[1], ARGS[2]
ntasks = length(ARGS) >= 3 ? parse(Int, ARGS[3]) : 8
tests = if length(ARGS) >= 4
    ARGS[4:end]
else
    cd(TESTDIR) do
        include(joinpath(TESTDIR, "choosetests.jl"))
        string.(@invokelatest(choosetests(String[])).tests)
    end
end
cd(() -> include(joinpath(TESTDIR, "testenv.jl")), TESTDIR)
const TIMEOUT = 20 * 60
const LOGDIR = mkpath(outfile * ".logs")
const FIELDS = ["allocator", "rss", "graphs", "content", "mapped", "wrbuf", "pp4k", "pp16k", "pp64k", "arenas"]

function run_test(t)
    # Same executable and flags as the test workers (see test/testenv.jl).
    cmd = addenv(`$test_exename $test_exeflags $(joinpath(DIR, "testsuite_one.jl")) $t`,
                 "JULIA_JIT_MM" => mode)
    out = Base.BufferStream()
    t0 = time()
    logfile = joinpath(LOGDIR, replace(t, '/' => '_') * ".log")
    p = run(pipeline(cmd; stdout=out, stderr=logfile); wait=false)
    timer = Timer(_ -> kill(p), TIMEOUT)
    wait(p); close(timer); close(out)
    s = read(out, String)
    line = findlast(l -> startswith(l, "RESULT "), split(s, '\n'))
    kv = Dict{String,String}()
    if line !== nothing
        for f in split(split(s, '\n')[line])[2:end]
            k, v = split(f, '='; limit=2)
            kv[k] = v
        end
    end
    status = line === nothing ? (process_exited(p) && p.termsignal != 0 ? "killed" : "noresult") : "ok"
    return (t, status, round(time() - t0; digits=1), kv)
end

open(outfile, "w") do io
    println(io, join(["test", "status", "seconds", FIELDS...], '\t'))
    flush(io)
    asyncmap(tests; ntasks) do t
        t, status, secs, kv = run_test(t)
        println(io, join([t, status, secs, (get(kv, f, "") for f in FIELDS)...], '\t'))
        flush(io)
        println(stderr, "done ", t, " ", status, " ", secs, "s")
    end
end
