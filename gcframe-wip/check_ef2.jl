using JuliaLowering, InteractiveUtils
using JuliaLowering: JuliaSyntax
# est_to_dst has "return_roots"="2" call sites (SyntaxTree pairs etc.)
sig = Tuple{typeof(JuliaLowering.expand_forms_2),
            JuliaLowering.DesugaringContext{Dict{Symbol, Dict{Int64, Any}}},
            JuliaSyntax.SyntaxTree{Dict{Symbol, Dict{Int64, Any}}}, Nothing}
buf = IOBuffer()
code_llvm(buf, InteractiveUtils.ArgInfo(sig); raw=true, dump_module=false, optimize=true, debuginfo=:none)
ir = String(take!(buf))
using Printf
for m in eachmatch(r"\"julia.return_roots\"=\"(\d+)\"", ir)
    global counts
end
counts = Dict{String,Int}()
for m in eachmatch(r"\"julia.return_roots\"=\"(\d+)\"", ir)
    counts[m.captures[1]] = get(counts, m.captures[1], 0) + 1
end
println("return_roots call sites by root count: ", counts)
gm = match(r"alloca \[(\d+) x ptr\], align 16", ir)
println("gcframe slots: ", gm === nothing ? "?" : gm.captures[1])
