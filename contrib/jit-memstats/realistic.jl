include(joinpath(@__DIR__, "common.jl"))
using Test, Random
const T = joinpath(Sys.BINDIR, "..", "..", "test")
for f in ("sorting.jl", "dict.jl", joinpath("strings", "basic.jl"))
    @eval Module() begin
        using Test, Random
        Base.include(@__MODULE__, $(joinpath(T, f)))
    end
end
report("realistic")
