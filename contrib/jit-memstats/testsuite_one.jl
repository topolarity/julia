# Runs one test file the way a test worker does, then reports the JIT counters.
# Usage (from test/): julia testsuite_one.jl <testname>
cd(joinpath(Sys.BINDIR, "..", "..", "test"))
using Distributed
include(joinpath(pwd(), "choosetests.jl"))
include(joinpath(pwd(), "testdefs.jl"))
include(joinpath(@__DIR__, "common.jl"))
name = ARGS[1]
# runtests.jl defines this progress printer for the workers to call.
print_testworker_started(name, wrkr) = nothing
try
    @invokelatest runtests(name, test_path(name))
catch err
    println(stderr, "test error: ", sprint(showerror, err))
end
report(name)
