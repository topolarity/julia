# Verify the trimmed `Trimmability` executable exercises a range of constructs
using Test

outdir = ARGS[1]

@testset "Trimmability" begin
    exe_suffix = splitext(Base.julia_exename())[2]
    trimmability_exe = joinpath(outdir, "bin", "trimmability" * exe_suffix)
    alllines = readlines(`$trimmability_exe arg1 arg2`)
    # A finalizer registered from reachable code must be kept and run at GC: its
    # target is reached only via the finalizer edge, not a static invoke. It runs
    # at a GC point, so exclude its line from the positional checks below.
    @test any(l -> l == "finalized resource 99", alllines)
    lines = filter(l -> l != "finalized resource 99", alllines)
    @test lines[1] == "Hello, world!"
    @test lines[2] == trimmability_exe
    @test lines[3] == "arg1"
    @test lines[4] == "arg2"
    @test lines[5] == "42"  # TypedCallable dispatched via its image-serialized adapter
    @test lines[6] == "42"  # top-level const TypedCallable, adapter from the live-cache sweep
    @test lines[7] == "123"  # OpaqueClosure built in reachable code: body CI kept, adapter emitted inline
    @test lines[8] == "42.0" # capture-free OpaqueClosure with a Float64 rt (different adapter)
    @test lines[9] == string(4.0+pi)
    @test parse(Float64, lines[10]) isa Float64
    @test lines[11] == "Version: 1.1.0"
    @test lines[12] == "# preferences: 0"
end
