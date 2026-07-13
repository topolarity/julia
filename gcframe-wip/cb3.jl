using JuliaLowering, InteractiveUtils
using JuliaLowering: JuliaSyntax
function framesize(sig)
    buf = IOBuffer()
    code_native(buf, InteractiveUtils.ArgInfo(sig); debuginfo=:none, dump_module=false)
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
T = Dict{Symbol, Dict{Int64, Any}}
sigs = [
    "expand_forms_2" => Tuple{typeof(JuliaLowering.expand_forms_2), JuliaLowering.DesugaringContext{T}, JuliaSyntax.SyntaxTree{T}, Nothing},
    "vst1" => Tuple{typeof(JuliaLowering.vst1), JuliaLowering.Validation1Context, JuliaSyntax.SyntaxTree{T}},
    "est_to_dst" => Tuple{typeof(JuliaLowering.est_to_dst), JuliaSyntax.SyntaxTree{T}},
    "compile" => Tuple{typeof(JuliaLowering.compile), JuliaLowering.LinearIRContext{T}, JuliaSyntax.SyntaxTree{T}, Bool, Bool},
    "_convert_closures" => Tuple{typeof(JuliaLowering._convert_closures), JuliaLowering.ClosureConversionCtx{T}, JuliaSyntax.SyntaxTree{T}},
]
# smoke: run the lowering pipeline first
JuliaLowering.include_string(Main, """
function smoke(x, y=2; z=3)
    acc = 0
    for i in 1:x
        acc += i > 5 ? i : -i
    end
    vals = [i^2 for i in 1:y if i != 2]
    f = w -> w + z
    t = (x, y..., 4)
    s = "interp \$(x)"
    return acc + f(1), vals, t, s
end
""")
r = Base.invokelatest(Main.smoke, 10)
println("smoke test: ", r[1] == 29 ? "OK" : "UNEXPECTED $(r[1])")
for (name, sig) in sigs
    println(rpad(name, 20), " frame total = ", framesize(sig))
end
