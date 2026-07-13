# Julia-level reproducer for the pointer-phi ("forwarder") shape: `c ? a : b`
# over an unboxed aggregate lowers to a memory phi whose edge copies are
# identical memcpys differing only in their source buffer; SimplifyCFG's
# sinking merges them into one memcpy reading through a `phi ptr` of the two
# buffers. Without forwarder-aware liveness in PreciseLifetimeEnds those
# buffers keep function-long live ranges and the frame scales with the number
# of units.
using InteractiveUtils

struct Blob      # 32 B, no pointers: stays an in-memory aggregate
    a::Int64
    b::Int64
    c::Int64
    d::Int64
end
@noinline mk(i::Int) = Blob(i, i + 1, i + 2, i + 3)
@noinline consume(t::Blob) = t.a + t.d

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

function irstats(f, types)
    buf = IOBuffer()
    code_llvm(buf, f, types; raw=true, dump_module=false, optimize=true, debuginfo=:none)
    ir = String(take!(buf))
    nphi = count("phi ptr", ir)
    nends = count("lifetime.end", ir)
    return (nphi, nends)
end

for N in (4, 16)
    body = [quote
        # s feeds the next unit's inputs: the reduction cannot be
        # reassociated into an end-of-function add tree, which would keep
        # every unit's result live at once (a register-pressure artifact
        # unrelated to stack lifetimes).
        a = mk(s + $(2i))
        b = mk(s + $(2i + 1))
        t = c ? a : b
        s += consume(t)
    end for i in 1:N]
    @eval @noinline function $(Symbol(:units_, N))(x::Int, c::Bool)
        s = x
        $(body...)
        return s
    end
end

for (name, f) in (("units_4", units_4), ("units_16", units_16))
    fs = framesize(f, (Int, Bool))
    nphi, nends = irstats(f, (Int, Bool))
    println(rpad(name, 12), " frame=", lpad(fs, 5), " B   ptr-phis=", nphi,
            "  lifetime.ends=", nends)
end
