using InteractiveUtils
include(joinpath(@__DIR__, "straight_gen_inc.jl"))
Core.eval(Main, straight_expr(65536))
Base.invokelatest(bench_f, 1.5)
buf = IOBuffer()
code_llvm(buf, bench_f, (Float64,); raw=true, dump_module=true, optimize=true, debuginfo=:none)
write(joinpath(@__DIR__, "final_module.ll"), take!(buf))
