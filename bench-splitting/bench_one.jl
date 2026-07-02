# One measurement for the JuliaFunctionSplitting flag sweep (driven by sweep.sh).
#
# ENV: SHAPE   = float | dual | tracked      (element type the RHS is specialized on)
#      SHAPEID = display name for the CSV (defaults to SHAPE; e.g. tracked_stock
#                when run against the registry ReverseDiff, whose fully-inlined
#                ops produce the many-small-blocks IR shape)
#      RD_N    = brusselator grid size; loads ../reversediff_fexpr_N$(RD_N).jl
#      LABEL   = flag-config id for the CSV
#
# Emits one CSV row:
#   shape,N,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ok
# compile_s is Julia's cold-compile time for the one specialization, llvm_s the
# LLVM opt+isel share of it, runtime_us the best of repeated calls (for tracked,
# one full tape recording with the tape emptied between reps).
using Printf
using ReverseDiff              # NaNMath is needed by the generated expression
const NaNMath = ReverseDiff.NaNMath
const shape = ENV["SHAPE"]
if shape == "dual"
    using ForwardDiff
end
const shapeid = get(ENV, "SHAPEID", shape)
const N = parse(Int, ENV["RD_N"])
const label = get(ENV, "LABEL", "?")

f! = include(joinpath(@__DIR__, "..", "reversediff_fexpr_N$(N).jl"))
n = 2 * N * N
u = rand(n)

tp = nothing
if shape == "float"
    uu = u; out = zeros(n)
elseif shape == "dual"
    uu = ForwardDiff.Dual{Nothing}.(u, randn(n)); out = similar(uu)
elseif shape == "tracked"
    tp = ReverseDiff.InstructionTape()
    uu = ReverseDiff.track(copy(u), tp); out = similar(uu)
else
    error("unknown SHAPE=$shape")
end

out_ref = zeros(n)
if shape != "float"
    f!(out_ref, u)   # Float64 reference (compiled before the timed target)
end

llvm_io = open(tempname(), "w+")
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), llvm_io.handle)
st = @timed f!(out, uu)
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), C_NULL)
flush(llvm_io); seekstart(llvm_io)
llvm_s = sum(parse(Int, m.captures[1]) for m in eachmatch(r"time_ns: (\d+)", read(llvm_io, String)); init=0) / 1e9

val(x) = shape == "float" ? x : shape == "dual" ? ForwardDiff.value(x) : ReverseDiff.value(x)
if shape == "float"
    out_ref .= out
end
ok = isapprox(val.(out), out_ref; rtol=1e-10)

best = Inf; reps = 0; t0 = time()
while reps < 5 || (time() - t0 < 0.3 && reps < 500)
    shape == "tracked" && empty!(tp)
    t = @elapsed f!(out, uu)
    global best = min(best, t); global reps += 1
end

@printf("%s,%d,%s,%.3f,%.3f,%.1f,%.1f,%d,%s\n",
        shapeid, N, label, st.compile_time, llvm_s,
        100 * llvm_s / max(st.compile_time, 1e-9), best * 1e6, reps, ok)
