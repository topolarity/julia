# Litmus test: gcframe/frame size must stay bounded as dispatch fan-out scales.
# Mirrors the lowering-walker shape: each branch builds SyntaxTree-like
# {tracked ptr, bits} values via sret-returning calls and passes them onward
# by pointer (staged argument roots).
using InteractiveUtils

struct Tree
    g::Vector{Int}   # tracked pointer (like SyntaxTree.graph)
    id::Int          # bits (like SyntaxTree.id)
end
@noinline mknode(g::Vector{Int}, k::Int) = Tree(g, k)
@noinline combine(a::Tree, b::Tree, c::Tree) = Tree(a.g, a.id + b.id + c.id)
@noinline consume(t::Tree) = t.id

function gen_dispatch(name, N)
    arms = String[]
    for k in 1:N
        push!(arms, """
        $(k == 1 ? "if" : "elseif") k == $k
            a = mknode(g, $k)
            b = mknode(g, $(k+1))
            c = combine(a, b, mknode(g, $(k+2)))
            r = consume(combine(a, c, b)) + consume(c)
        """)
    end
    src = "function $name(g::Vector{Int}, k::Int)\n r = 0\n" * join(arms) *
          "\nelse\n r = -1\nend\n return r\nend"
    include_string(Main, src)
end

function measure(f, N)
    buf = IOBuffer()
    code_native(buf, f, (Vector{Int}, Int); debuginfo=:none, dump_module=false, syntax=:intel)
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
    code_llvm(buf2, f, (Vector{Int}, Int); raw=true, dump_module=false, optimize=true, debuginfo=:none)
    ir = String(take!(buf2))
    gm = match(r"%gcframe\d* = alloca \[(\d+) x ptr\]", ir)
    println("N=$(lpad(N,4))  frame=$(lpad(subsz + 8*pushes + 8,6)) B   gcframe=$(gm === nothing ? 0 : parse(Int, gm.captures[1])) slots")
end

for N in (25, 50, 100, 200)
    name = Symbol("dispatch_$N")
    gen_dispatch(name, N)
    f = getfield(Main, name)
    Base.invokelatest(f, Int[], 3)  # smoke
    measure(f, N)
end
