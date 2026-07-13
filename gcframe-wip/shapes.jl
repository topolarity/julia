# CFG-shape matrix for stack/gcframe behavior: measures machine frame size and
# GC frame slots for straight-line code, live-overlap controls, loops, and
# fan-out-in-loop shapes, at two sizes each to expose scaling.
using InteractiveUtils

struct TB          # tracked + bits: returned via sret + return_roots (split value)
    a::Any
    b::Int
end
const CONST_OBJ = "const"
@noinline mk(i::Int) = TB(CONST_OBJ, i)
@noinline consume(t::TB) = t.b
@noinline consume2(t::TB, u::TB) = t.b + u.b

function framesize(f, types)
    buf = IOBuffer()
    code_native(buf, f, types; debuginfo=:none, dump_module=false)
    asm = String(take!(buf))
    subsz = 0; pushes = 0
    for line in eachline(IOBuffer(asm))
        l = strip(line)
        isempty(l) && continue
        startswith(l, "push") && (pushes += 1; continue)
        m = match(r"^sub\s+rsp,\s*(\d+)", l)
        m !== nothing && (subsz += parse(Int, m.captures[1]); continue)
        m = match(r"^sub\s+r11,\s*(\d+)", l)
        m !== nothing && (subsz += parse(Int, m.captures[1]); continue)
        (occursin(r"^mov\s+qword\s+ptr\s+\[rsp\],\s*0$", l) || occursin(r"^mov\s+r11,\s*rsp$", l) ||
         occursin(r"^cmp\s+rsp,\s*r11$", l) || startswith(l, "jne") || startswith(l, ".") ||
         startswith(l, "L") || occursin(r"^mov\s+rbp,\s*rsp$", l)) && continue
        break
    end
    return subsz + 8*pushes + 8
end

function gcslots(f, types)
    buf = IOBuffer()
    code_llvm(buf, f, types; raw=true, dump_module=false, optimize=true, debuginfo=:none)
    ir = String(take!(buf))
    gm = match(r"%gcframe\d* = alloca \[(\d+) x ptr\]", ir)
    gm === nothing ? 0 : parse(Int, gm.captures[1])
end

# 1. Straight line, temps die immediately. Ideal: O(1) slots.
for N in (4, 16)
    body = [:(s += consume(mk(x + $i))) for i in 1:N]
    @eval @noinline function $(Symbol(:straight_, N))(x::Int)
        s = x
        $(body...)
        return s
    end
end

# 2. Straight line, all temps live to the end (control: frame MUST scale).
for N in (4, 16)
    vars = [Symbol(:t, i) for i in 1:N]
    mks  = [:($(vars[i]) = mk(x + $i)) for i in 1:N]
    uses = [:(s += consume($(vars[i]))) for i in 1:N]
    @eval @noinline function $(Symbol(:straight_live_, N))(x::Int)
        s = x
        $(mks...)
        $(uses...)
        return s
    end
end

# 3. Straight-line body inside a loop.
for N in (4, 16)
    body = [:(s += consume(mk(j + $i))) for i in 1:N]
    @eval @noinline function $(Symbol(:loop_straight_, N))(n::Int)
        s = 0
        for j in 1:n
            $(body...)
        end
        return s
    end
end

# 4. Fan-out inside a loop (mini kind-switch per iteration).
for N in (4, 16)
    arms = Expr(:if, :(k == 1), :(s += consume(mk(j))))
    cur = arms
    for i in 2:N
        nxt = Expr(:elseif, :(k == $i), :(s += consume(mk(j + $i))))
        push!(cur.args, nxt)
        cur = nxt
    end
    push!(cur.args, :(s -= 1))
    @eval @noinline function $(Symbol(:loop_fanout_, N))(n::Int)
        s = 0
        for j in 1:n
            k = s % $N + 1
            $arms
        end
        return s
    end
end

# 5. Bounds-check staging inside a loop (throw args staged per iteration).
@noinline function loop_boundscheck(a::Vector{Int}, n::Int)
    s = 0
    for j in 1:n
        s += a[j] + a[j+1] + a[j+2] + a[j+3]
    end
    return s
end

# 6. Two-at-a-time consumption (pairs overlap briefly). Ideal: 2 slots.
for N in (4, 16)
    body = [:(s += consume2(mk(x + $i), mk(x + $(i + 100)))) for i in 1:N]
    @eval @noinline function $(Symbol(:pairs_, N))(x::Int)
        s = x
        $(body...)
        return s
    end
end

# warm up / force compilation, then measure
cases = Any[
    ("straight_4",      straight_4,      (Int,)),
    ("straight_16",     straight_16,     (Int,)),
    ("straight_live_4", straight_live_4, (Int,)),
    ("straight_live_16",straight_live_16,(Int,)),
    ("pairs_4",         pairs_4,         (Int,)),
    ("pairs_16",        pairs_16,        (Int,)),
    ("loop_straight_4", loop_straight_4, (Int,)),
    ("loop_straight_16",loop_straight_16,(Int,)),
    ("loop_fanout_4",   loop_fanout_4,   (Int,)),
    ("loop_fanout_16",  loop_fanout_16,  (Int,)),
    ("loop_boundscheck",loop_boundscheck,(Vector{Int}, Int)),
]
println(rpad("shape", 20), lpad("frame B", 8), lpad("gcframe", 8))
for (name, f, ts) in cases
    println(rpad(name, 20), lpad(framesize(f, ts), 8), lpad(gcslots(f, ts), 8))
end
