# MTK-free ReverseDiff compile-scaling MWE. Needs reversediff_fexpr_N$(N).jl next to it.
using ReverseDiff, Printf
const NaNMath = ReverseDiff.NaNMath  # avoid needing NaNMath in the env
N = parse(Int, get(ENV, "RD_N", "6"))
f! = include(joinpath(@__DIR__, "reversediff_fexpr_N$(N).jl"))
n = 2 * N * N
tp = ReverseDiff.InstructionTape()
u_t = ReverseDiff.track(rand(n), tp); out_t = similar(u_t)
# Warm up ReverseDiff's tracked scalar ops so the timing below isolates the
# generated function itself.
let g! = (o, u) -> (o[1] = u[1] * u[2] + u[1] / u[2] - u[1]^2; o),
    tp2 = ReverseDiff.InstructionTape()
    uu = ReverseDiff.track(rand(2), tp2)
    g!(similar(uu), uu)
end
llvm_io = open(tempname(), "w+")
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), llvm_io.handle)
stats = @timed f!(out_t, u_t)
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), C_NULL)
flush(llvm_io); seekstart(llvm_io)
yaml = read(llvm_io, String)
llvm_ns = sum(parse(Int, m.captures[1]) for m in eachmatch(r"time_ns: (\d+)", yaml); init=0)
@printf("N=%d  wall=%.2fs  compile=%.2fs  llvm-opt+isel=%.2fs  (llvm share of compile: %.0f%%)\n",
        N, stats.time, stats.compile_time, llvm_ns / 1e9, 100 * llvm_ns / 1e9 / stats.compile_time)
