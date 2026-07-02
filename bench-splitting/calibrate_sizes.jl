# Calibrates the size units the pass thresholds use: for each shape/N, compile
# the RHS once with the jl_dump_llvm_opt stats enabled and report the largest
# function's unoptimized LLVM instruction and basic-block counts alongside the
# typed-IR statement count. Thresholds gate on LLVM instructions at pass time
# (after DCE/SimplifyCFG/SROA/EarlyCSE, i.e. somewhat below the "before" count
# printed here).
#
# ENV: SHAPE, RD_N as in bench_one.jl. Emits:
#   shape,N,typed_stmts,max_fn_llvm_insts,max_fn_blocks,biggest_block_est
using Printf, InteractiveUtils
using ReverseDiff
const NaNMath = ReverseDiff.NaNMath
const shape = ENV["SHAPE"]
if shape == "dual"
    using ForwardDiff
end
const N = parse(Int, ENV["RD_N"])
f! = include(joinpath(@__DIR__, "..", "reversediff_fexpr_N$(N).jl"))
n = 2 * N * N
u = rand(n)
if shape == "float"
    uu = u; out = zeros(n)
elseif shape == "dual"
    uu = ForwardDiff.Dual{Nothing}.(u, randn(n)); out = similar(uu)
else
    tp = ReverseDiff.InstructionTape()
    uu = ReverseDiff.track(copy(u), tp); out = similar(uu)
end
stmts = length(first(only(code_typed(f!, (typeof(out), typeof(uu))))).code)
io = open(tempname(), "w+")
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), io.handle)
f!(out, uu)
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), C_NULL)
flush(io); seekstart(io)
txt = read(io, String)
best_i = 0; best_b = 0
for m in eachmatch(r"instructions: (\d+)\n\s+basicblocks: (\d+)", txt)
    i = parse(Int, m.captures[1]); b = parse(Int, m.captures[2])
    if i > best_i
        global best_i = i; global best_b = b
    end
end
@printf("%s,%d,%d,%d,%d,%d\n", shape, N, stmts, best_i, best_b, best_i ÷ max(best_b, 1))
