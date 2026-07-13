# Reproducers for the marker coverage gaps: allocas created outside the
# recorded emit_new_struct/split_value/value_to_pointer/phi sites. Each unit
# lives in its own mutually exclusive branch, so with markers StackColoring
# collapses the frame to ~one unit; without markers the frame is the sum.
using InteractiveUtils

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
        (occursin(r"^mov\s+qword\s+ptr\s+\[rsp\],\s*0$", l) || occursin(r"^mov\s+r11,\s*rsp$", l) ||
         occursin(r"^cmp\s+rsp,\s*r11$", l) || startswith(l, "jne") || startswith(l, ".") ||
         startswith(l, "L") || occursin(r"^mov\s+rbp,\s*rsp$", l)) && continue
        break
    end
    return subsz + 8*pushes + 8
end

# --- gap 1: ccall sret result buffers (ccall.cpp "result") ------------------
# A @cfunction returning a 4-Int tuple uses the C sret convention: every
# call site allocates an unmarked result buffer.
mkquad(x::Int) = (x, x + 1, x + 2, x + 3)
const QUAD_PTR = @cfunction(mkquad, NTuple{4,Int}, (Int,))
@noinline useq(t::NTuple{4,Int}) = t[1] + t[4]

# --- gap 2: union payload allocas (try_emit_union_alloca) -------------------
@noinline pick(c::Bool, x::Int) = c ? x : Float64(x)
@noinline usev(v) = v isa Int ? v : Int(v::Float64)

# --- gap 3: immutable-union field copies (typed_load) -----------------------
struct HasU
    a::Union{NTuple{3,Int}, Float64}
    b::Int
end
@noinline mku(x::Int) = HasU((x, x+1, x+2), x)
@noinline useu(u) = u isa Float64 ? Int(u) : (u::NTuple{3,Int})[1]

for N in (4, 16)
    cc = [quote
        if k == $i
            t = ccall(QUAD_PTR, NTuple{4,Int}, (Int,), x + $i)
            return useq(t)
        end
    end for i in 1:N]
    @eval @noinline function $(Symbol(:ccall_, N))(k::Int, x::Int)
        $(cc...)
        return 0
    end
    un = [quote
        if k == $i
            v = pick(c, x + $i)
            return usev(v)
        end
    end for i in 1:N]
    @eval @noinline function $(Symbol(:union_, N))(k::Int, c::Bool, x::Int)
        $(un...)
        return 0
    end
    fl = [quote
        if k == $i
            u = mku(x + $i)
            return useu(u.a)
        end
    end for i in 1:N]
    @eval @noinline function $(Symbol(:uload_, N))(k::Int, x::Int)
        $(fl...)
        return 0
    end
end

println("shape          N=4    N=16")
for (name, f4, f16, ts) in (
        ("ccall_sret", ccall_4, ccall_16, (Int, Int)),
        ("union_alloca", union_4, union_16, (Int, Bool, Int)),
        ("union_load", uload_4, uload_16, (Int, Int)))
    println(rpad(name, 13), lpad(framesize(f4, ts), 5), lpad(framesize(f16, ts), 8))
end
