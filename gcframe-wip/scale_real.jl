# Scale the REAL expand_forms_2 by duplicating its arms M times, each copy
# guarded by an opaque load so it stays live, then measure frame/gcframe.
using JuliaLowering, InteractiveUtils
using JuliaLowering: JuliaSyntax

text = read(joinpath(@__DIR__, "..", "JuliaLowering", "src", "desugaring.jl"), String)
startidx = findfirst("function expand_forms_2(ctx::DesugaringContext, ex::SyntaxTree, docs=nothing)", text)
fex, _ = Meta.parse(text, first(startidx))
@assert Meta.isexpr(fex, :function)

Core.eval(JuliaLowering, :(const SCALE_GUARD = fill(false, 100_000)))

function collect_arms(ifex)
    arms = Any[]
    cur = ifex
    while true
        push!(arms, (cur.args[1], cur.args[2]))
        tail = length(cur.args) == 3 ? cur.args[3] : nothing
        if tail isa Expr && tail.head === :elseif
            cur = tail
        else
            return arms, tail
        end
    end
end

# The copy's condition must be UNRELATED to the original arm's, or GVN
# proves it false on the fall-through edge and deletes the copy.
add_guard(cond, n) = :(SCALE_GUARD[$n]::Bool)
# elseif conditions are block-wrapped (LineNumberNode + cond)
guard_wrapped(c, n) = if c isa Expr && c.head === :block
    Expr(:block, c.args[1:end-1]..., add_guard(c.args[end], n))
else
    add_guard(c, n)
end

function build_scaled(fex, M, name)
    fex = deepcopy(fex)
    body = fex.args[2]
    ifpos = findfirst(a -> Meta.isexpr(a, :if), body.args)
    arms, elsetail = collect_arms(body.args[ifpos])
    n = 0
    tail = elsetail
    for (cond, then) in reverse(arms)
        for j in M:-1:1
            n += 1
            c = j == 1 ? deepcopy(cond) : guard_wrapped(deepcopy(cond), n)
            tail = Expr(:elseif, c isa Expr && c.head === :block ? c : Expr(:block, LineNumberNode(0), c),
                        deepcopy(then), tail)
        end
    end
    # convert outermost elseif into if (unwrap block-wrapped condition)
    c0 = tail.args[1]
    cond0 = c0 isa Expr && c0.head === :block ? c0.args[end] : c0
    body.args[ifpos] = Expr(:if, cond0, tail.args[2], tail.args[3])
    # rename
    sig = fex.args[1]
    callee = sig
    while Meta.isexpr(callee, :call) == false
        callee = callee.args[1]
    end
    callee.args[1] = name
    println("arms: ", length(arms), " -> ", n)
    Core.eval(JuliaLowering, fex)
end

function measure(f, label)
    T = Dict{Symbol, Dict{Int64, Any}}
    sig = Tuple{typeof(f), JuliaLowering.DesugaringContext{T}, JuliaSyntax.SyntaxTree{T}, Nothing}
    buf = IOBuffer()
    code_native(buf, InteractiveUtils.ArgInfo(sig); debuginfo=:none, dump_module=false)
    asm = String(take!(buf))
    subsz = 0; pushes = 0
    for line in eachline(IOBuffer(asm))
        l = strip(line); isempty(l) && continue
        startswith(l, "push") && (pushes += 1; continue)
        m = match(r"^sub\s+rsp,\s*(\d+)", l); m !== nothing && (subsz += parse(Int, m.captures[1]); continue)
        m = match(r"^sub\s+r11,\s*(\d+)", l); m !== nothing && (subsz += parse(Int, m.captures[1]); continue)
        (occursin(r"^mov\s+qword\s+ptr\s+\[rsp\],\s*0$", l) || occursin(r"^mov\s+r11,\s*rsp$", l) ||
         occursin(r"^cmp\s+rsp,\s*r11$", l) || startswith(l, "jne") || startswith(l, ".") ||
         startswith(l, "L") || occursin(r"^mov\s+rbp,\s*rsp$", l)) && continue
        break
    end
    buf2 = IOBuffer()
    code_llvm(buf2, InteractiveUtils.ArgInfo(sig); raw=true, dump_module=false, optimize=true, debuginfo=:none)
    ir = String(take!(buf2))
    gm = match(r"%gcframe\d* = alloca \[(\d+) x ptr\]", ir)
    println("$label  frame=$(lpad(subsz + 8*pushes + 8, 6)) B   gcframe=$(gm === nothing ? 0 : parse(Int, gm.captures[1])) slots")
end

measure(JuliaLowering.expand_forms_2, "M=1 (original)   ")
for M in (2, 4)
    name = Symbol("expand_forms_2_scaled_$M")
    build_scaled(fex, M, name)
    f = getfield(JuliaLowering, name)
    measure(f, "M=$M (scaled)     ")
end
