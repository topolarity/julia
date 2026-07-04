# One measurement on a synthetic function that scales exactly one IR-shape axis
# (driven by sweep_axes.sh). Unlike the MTK composite benchmark, each generator
# moves a single quantity so the pass thresholds can be tuned independently.
#
# ENV: GEN   = straight | blocks | calls
#        straight: S muladds over 8 dependent chains in ONE basic block.
#                  All 8 chains are live across any cut -> worst case for the
#                  runtime cost of chunk boundaries in dense scalar math.
#        blocks:   S float statements in real branches of ~B statements each
#                  (conditionally-updated chains -> phis; arms too big to
#                  if-convert). Scales function size with block size pinned.
#        calls:    C calls to a @noinline allocating leaf, threaded through W
#                  parallel Ref chains -> every call is a safepoint with W live
#                  tracked values. B > 0 inserts a real branch every B calls
#                  (pins block size); B = 0 leaves one giant block.
#      S = size parameter (statements for straight/blocks, calls for calls)
#      B = block-size parameter (blocks/calls), W = live-root width (calls)
#      LABEL = flag-config id
#
# Emits: gen,S,B,W,label,compile_s,llvm_s,llvm_pct,runtime_us,reps,ns_per_op,chk
# ns_per_op normalizes runtime by EXECUTED operation count: blocks() executes
# only one arm per diamond (~S/2 ops), so raw runtimes are not comparable
# across generators at equal S.
using Printf

const GEN = ENV["GEN"]
const S = parse(Int, ENV["S"])
const B = parse(Int, get(ENV, "B", "0"))
const W = parse(Int, get(ENV, "W", "8"))
const label = get(ENV, "LABEL", "?")

chain(i) = Symbol(:v, i)

function straight_expr(S)
    stmts = Expr[]
    for i in 1:8
        push!(stmts, :($(chain(i)) = x + $(float(i))))
    end
    for k in 0:S-1
        i = k % 8 + 1
        push!(stmts, :($(chain(i)) = muladd($(chain(i)), 1.0000001, $(float(k % 7)))))
    end
    push!(stmts, :(return $(Expr(:call, :+, (chain(i) for i in 1:8)...))))
    :(function bench_f(x::Float64)
        $(Expr(:block, stmts...))
    end)
end

function blocks_expr(S, B)
    B = max(B, 24)              # arms below ~10 statements get if-converted
    nb = cld(S, B)
    stmts = Expr[]
    for i in 1:8
        push!(stmts, :($(chain(i)) = x + $(float(i))))
    end
    arm(lo, cnt) = Expr(:block, (:($(chain(k % 8 + 1)) = muladd($(chain(k % 8 + 1)), 1.0000001, $(float(k % 7)))) for k in lo:lo+cnt-1)...)
    half = B ÷ 2
    for b in 0:nb-1
        push!(stmts, Expr(:if, :($(chain(b % 8 + 1)) > $(float(b % 13) - 6.0)),
                          arm(b * B, half), arm(b * B + half, B - half)))
    end
    push!(stmts, :(return $(Expr(:call, :+, (chain(i) for i in 1:8)...))))
    :(function bench_f(x::Float64)
        $(Expr(:block, stmts...))
    end)
end

function calls_expr(C, W, B)
    rr(i) = Symbol(:r, i)
    stmts = Expr[]
    for i in 1:W
        push!(stmts, :($(rr(i)) = Base.RefValue(x + $(float(i)))))
    end
    for k in 0:C-1
        i = k % W + 1
        push!(stmts, :($(rr(i)) = bench_leaf($(rr(i)), $(float(k % 5)))))
        if B > 0 && (k + 1) % B == 0
            push!(stmts, Expr(:if, :($(rr(i))[] > $(float(k % 11) - 5.0)),
                              :($(rr(1)) = bench_leaf($(rr(1)), 1.0)),
                              :($(rr(min(2, W))) = bench_leaf($(rr(min(2, W))), 2.0))))
        end
    end
    push!(stmts, :(return $(Expr(:call, :+, (:($(rr(i))[]) for i in 1:W)...))))
    :(function bench_f(x::Float64)
        $(Expr(:block, stmts...))
    end)
end

@noinline bench_leaf(r::Base.RefValue{Float64}, x::Float64) = Base.RefValue(muladd(r[], 0.99999, x))

# arrays: like straight, but from k >= S/4 the addends come from a Vector
# fetched once from a const Ref (a runtime tracked value — a const global's
# data pointer would constant-fold away), with an occasional store into it.
# EarlyCSE (pre-split) CSEs the element derivation spines (memoryref getfield
# -> julia.gc_loaded -> GEP) at their first occurrence — mid-block, so past
# the entry chunk and inside an extracted region — and the stores keep the
# loads from being CSE'd, so the derived (AS11/AS13) pointers themselves stay
# live across every later chunk boundary: derived *outputs*, exercising
# rematerializeDerivedOutputs, which the pure-FP shapes never hit.
function arrays_expr(S)
    stmts = Expr[]
    push!(stmts, :(A = BENCH_REF[]))
    for i in 1:8
        push!(stmts, :($(chain(i)) = x + $(float(i))))
    end
    for k in 0:S-1
        i = k % 8 + 1
        if k < S ÷ 4
            push!(stmts, :($(chain(i)) = muladd($(chain(i)), 1.0000001, $(float(k % 7)))))
            continue
        end
        if k % 512 == 0
            push!(stmts, Expr(:macrocall, Symbol("@inbounds"), LineNumberNode(0),
                              :(A[$(k % 7 + 1)] = 1.0 + $(chain(i)) * 1.0e-9)))
        end
        elt = Expr(:macrocall, Symbol("@inbounds"), LineNumberNode(0),
                   :(A[$(k % 7 + 1)]))
        push!(stmts, :($(chain(i)) = muladd($(chain(i)), 1.0000001, $elt)))
    end
    push!(stmts, :(return $(Expr(:call, :+, (chain(i) for i in 1:8)...))))
    :(function bench_f(x::Float64)
        $(Expr(:block, stmts...))
    end)
end

GEN == "arrays" && Core.eval(Main, :(const BENCH_REF = Ref{Vector{Float64}}(collect(0.0:6.0))))
ex = GEN == "straight" ? straight_expr(S) :
     GEN == "blocks"   ? blocks_expr(S, B) :
     GEN == "calls"    ? calls_expr(S, W, B) :
     GEN == "arrays"   ? arrays_expr(S) : error("unknown GEN=$GEN")
Core.eval(Main, ex)

llvm_io = open(tempname(), "w+")
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), llvm_io.handle)
st = @timed Base.invokelatest(bench_f, 1.5)
ccall(:jl_dump_llvm_opt, Nothing, (Ptr{Nothing},), C_NULL)
flush(llvm_io); seekstart(llvm_io)
yaml = read(llvm_io, String)
llvm_s = sum(parse(Int, m.captures[1]) for m in eachmatch(r"time_ns: (\d+)", yaml); init=0) / 1e9
if get(ENV, "STATS", "0") == "1"
    nb = na = 0
    for entry in split(yaml, "\n- \n")
        global nb, na
        parts = split(entry, "  after: ")
        cnt(x) = sum(parse(Int, m.captures[1]) for m in eachmatch(r"instructions: (\d+)", x); init=0)
        nb += cnt(parts[1])
        length(parts) > 1 && (na += cnt(parts[2]))
    end
    println(stderr, "MODSTATS before=", nb, " after=", na)
end

best = Inf; reps = 0; t0 = time()
while reps < 5 || (time() - t0 < 0.3 && reps < 10000)
    t = @elapsed Base.invokelatest(bench_f, 1.5)
    global best = min(best, t); global reps += 1
end

# PERFMODE=1: after the timed measurement, announce readiness and spin the
# hot loop for LOOPSECS wall seconds so an external `perf stat -p` can sample
# a steady state. Iteration count is printed for per-iteration normalization
# (use rates: counters/sec vs iters/sec).
if get(ENV, "PERFMODE", "0") == "1"
    println(stderr, "PERFREADY pid=", getpid()); flush(stderr)
    sleep(2)  # attach window
    t_end = time() + parse(Float64, get(ENV, "LOOPSECS", "30"))
    it = 0
    t0p = time()
    while time() < t_end
        Base.invokelatest(bench_f, 1.5)
        global it += 1
    end
    println(stderr, "PERFDONE iters=", it, " secs=", round(time() - t0p; digits=3))
    flush(stderr)
end

work = GEN == "blocks" ? S ÷ 2 : S   # blocks() executes one arm per diamond
@printf("%s,%d,%d,%d,%s,%.3f,%.3f,%.1f,%.2f,%d,%.3f,%s\n",
        GEN, S, B, W, label, st.compile_time, llvm_s,
        100 * llvm_s / max(st.compile_time, 1e-9), best * 1e6, reps,
        best * 1e9 / work, isfinite(st.value))
