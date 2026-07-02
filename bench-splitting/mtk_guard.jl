# Why is compiling the brusselator body for ReverseDiff tracked types so much costlier than
# for Float64 (or even ForwardDiff.Dual)? Hypothesis: each tracked scalar op inlines recording
# machinery, multiplying the optimized-IR size the compiler must chew through; inference/optim
# are super-linear in IR size. Measure typed-IR statement count + compile time for the SAME
# body specialized on Float64, Dual{1}, and TrackedReal.
#using Pkg
#Pkg.activate(temp=true)
#Pkg.add(["ModelingToolkit", "Symbolics", "ReverseDiff", "ForwardDiff", "Printf", "InteractiveUtils"])
using ModelingToolkit
using ModelingToolkit: t_nounits as t, D_nounits as D
import ModelingToolkit as MTK
using Symbolics
using ReverseDiff, ForwardDiff, Printf
using InteractiveUtils

const Ns = [4]

function get_rhs(N)
    xyd = range(0, stop = 1, length = N); dx = step(xyd)
    wrap(a) = a == N + 1 ? 1 : a == 0 ? N : a
    @parameters A=3.4 B=1.0 alpha=10.0
    uu = [only(@variables $(Symbol("u_$(i)_$(j)"))(t)) for i in 1:N, j in 1:N]
    vv = [only(@variables $(Symbol("v_$(i)_$(j)"))(t)) for i in 1:N, j in 1:N]
    eqs = Equation[]
    for i in 1:N, j in 1:N
        ip, im, jp, jm = wrap(i + 1), wrap(i - 1), wrap(j + 1), wrap(j - 1)
        lap_u = uu[im, j] + uu[ip, j] + uu[i, jm] + uu[i, jp] - 4uu[i, j]
        lap_v = vv[im, j] + vv[ip, j] + vv[i, jm] + vv[i, jp] - 4vv[i, j]
        push!(eqs, D(uu[i, j]) ~ alpha / dx^2 * lap_u + B + uu[i, j]^2 * vv[i, j] - (A + 1) * uu[i, j])
        push!(eqs, D(vv[i, j]) ~ alpha / dx^2 * lap_v + A * uu[i, j] - uu[i, j]^2 * vv[i, j])
    end
    @named brusselator = System(eqs, t, vcat(vec(uu), vec(vv)), [A, B, alpha])
    sys = mtkcompile(brusselator)
    syms = unknowns(sys)
    pmap = Dict(A => 3.4, B => 1.0, alpha => 10.0)
    rhs = [Symbolics.substitute(eq.rhs, pmap) for eq in MTK.full_equations(sys)]
    return rhs, syms
end

for N in Ns
    rhs, syms = get_rhs(N)
    n = length(syms)
    # @eval the expression form (not a RuntimeGeneratedFunction) so code_typed sees the real,
    # inlined body rather than just the RGF wrapper.
    f_expr = build_function(rhs, syms; expression = Val{true}, cse = true)[2]
    f! = @eval $f_expr

    # three input flavors
    u_f = rand(n);                                   out_f = similar(u_f)
    u_d = ForwardDiff.Dual{Nothing}.(rand(n), randn(n)); out_d = similar(u_d)
    tp  = ReverseDiff.InstructionTape()
    u_t = ReverseDiff.track(rand(n), tp);            out_t = similar(u_t)

    # optimized typed-IR statement count (post-inlining) for each specialization
    irlen(args) = length(first(only(code_typed(f!, args))).code)
    ir_f = irlen((typeof(out_f), typeof(u_f)))
    ir_d = irlen((typeof(out_d), typeof(u_d)))
    ir_t = irlen((typeof(out_t), typeof(u_t)))

    # cold compile time (Julia compilation only) per specialization
    cf = (@timed f!(out_f, u_f)).compile_time
    cd = (@timed f!(out_d, u_d)).compile_time
    ct = (@timed f!(out_t, u_t)).compile_time

    @printf("\n=== compiling the SAME RHS body for different element types (N=%d, %d eqs) ===\n", N, n)
    @printf("%-22s %14s %12s %14s %12s\n", "eltype", "typed-IR stmts", "vs Float64", "compile(s)", "vs Float64")
    println("-"^78)
    @printf("%-22s %14d %12s %14.3f %12s\n", "Float64",              ir_f, "1.0x",                         cf, "1.0x")
    @printf("%-22s %14d %11.1fx %14.3f %11.1fx\n", "ForwardDiff.Dual{1}", ir_d, ir_d / ir_f,               cd, cd / max(1e-9, cf))
    @printf("%-22s %14d %11.1fx %14.3f %11.1fx\n", "ReverseDiff.TrackedReal", ir_t, ir_t / ir_f,           ct, ct / max(1e-9, cf))
end

InteractiveUtils.versioninfo(stderr)
