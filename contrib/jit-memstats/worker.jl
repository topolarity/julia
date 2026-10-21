# Runs test files one after another in one process, like a test worker, and
# reports the JIT counters after each one.
# Usage: julia <test worker flags> worker.jl <testname>...
cd(joinpath(Sys.BINDIR, "..", "..", "test"))
using Distributed
include(joinpath(pwd(), "choosetests.jl"))
include(joinpath(pwd(), "testdefs.jl"))
include(joinpath(@__DIR__, "common.jl"))
# runtests.jl defines this progress printer for the workers to call.
print_testworker_started(name, wrkr) = nothing
for name in ARGS
    try
        @invokelatest runtests(name, test_path(name))
    catch err
        println(stderr, "test error in $name: ", sprint(showerror, err))
    end
    report(name)
    flush(stdout)
end
