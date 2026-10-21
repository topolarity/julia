include(joinpath(@__DIR__, "common.jl"))
for i in 1:3000
    f = @eval $(Symbol(:f_, i))(x) = x * $i + 1
    Base.invokelatest(f, 2)
end
report("many_small")
