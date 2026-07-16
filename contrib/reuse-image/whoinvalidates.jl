# Attribute method-insertion invalidations caused by a workload.
#
#   julia [--project=...] whoinvalidates.jl "using Plots" [FocusModule.name]
#
# Prints every insertion trigger ranked by total invalidated CodeInstances,
# with a per-module breakdown of the victims. With a third argument
# (e.g. "REPLCompletions.InferenceParams"), also prints the *direct* (depth-0)
# victims of that trigger — the MethodInstances that actually hold the
# intersecting method-match edges; everything else in the tree is transitive
# backedge fallout, so the direct victims are where a fix must aim.
#
# Pitfalls this tool avoids (learned the hard way):
#  * parentmodule(Compiler) === Base, so classifying victims by their *root*
#    module hides the compiler entirely. Match the full parent chain.
#  * Trigger victim counts shift when an earlier trigger is fixed (a CI killed
#    by the first intersecting insertion can't be counted for the second), so
#    compare totals only across runs of the same build.
workload = ARGS[1]
focus = length(ARGS) >= 2 ? ARGS[2] : nothing

invs = ccall(:jl_debug_method_invalidation, Any, (Cint,), 1)
Core.eval(Main, Meta.parseall(workload))
ccall(:jl_debug_method_invalidation, Any, (Cint,), 0)

mi_of(x) = x isa Core.MethodInstance ? x :
           x isa Core.CodeInstance ? (x.def isa Core.MethodInstance ? x.def : x.def.def) :
           nothing
inmodule(m::Module, name::String) = begin
    while true
        string(nameof(m)) == name && return true
        parentmodule(m) === m && return false
        m = parentmodule(m)
    end
end

block = Any[]
totals = Dict{Any,Int}()
vmods = Dict{Any,Dict{String,Int}}()
i = 1
while i <= length(invs)
    x = invs[i]
    if x isa Method && i < length(invs) && invs[i+1] isa String &&
       (occursin("insert", invs[i+1]::String) || occursin("disable", invs[i+1]::String))
        n = 0; mods = Dict{String,Int}()
        for it in block
            mi = mi_of(it); mi === nothing && continue
            n += 1
            d = mi.def
            mods[d isa Method ? string(d.module) : "toplevel"] =
                get(mods, d isa Method ? string(d.module) : "toplevel", 0) + 1
        end
        if n > 0
            totals[x] = get(totals, x, 0) + n
            vmods[x] = mods
        end
        if focus !== nothing && string(x.module, ".", x.name) == focus
            d0 = Dict{Any,Int}()
            j = 1
            while j <= length(block)
                mi = mi_of(block[j])
                if mi !== nothing && j < length(block) && block[j+1] isa Int32 && block[j+1] == 0
                    d0[mi.specTypes] = get(d0, mi.specTypes, 0) + 1
                    j += 2
                else
                    j += 1
                end
            end
            println("\n== direct (depth-0) victims of ", focus, ": ", length(d0), " ==")
            for (st, c) in sort!(collect(d0); by=x->-x[2])[1:min(end,20)]
                println("  ", st)
            end
        end
        empty!(block); global i += 2; continue
    end
    push!(block, x); global i += 1
end

println("== triggers by total invalidated CodeInstances ==")
for (m, c) in sort!(collect(totals); by=last, rev=true)[1:min(end,20)]
    top = sort!(collect(vmods[m]); by=last, rev=true)[1:min(end,5)]
    println(lpad(c, 5), "  ", m.module, ".", m.name, " @ ", basename(string(m.file)), ":", m.line)
    println("       victims: ", join(["$k=$v" for (k, v) in top], " "))
end
