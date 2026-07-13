# End-to-end JuliaLowering wall-time benchmark: lowers each top-level
# statement of some large Base files, timing the lowering loop only (parsing
# is redone per iteration, untimed). Run with JULIA_OBJCACHE=0 and
# --compiled-modules=no so the measured code is compiled by this build's own
# pipeline.
using JuliaLowering
using JuliaLowering: JuliaSyntax

function parsefile(text, name)
    stream = JuliaSyntax.ParseStream(text)
    JuliaSyntax.parse!(stream; rule=:all)
    return JuliaSyntax.build_tree(JuliaSyntax.SyntaxTree, stream; filename=name)
end

function lower_all(tree)
    mod = Module(:Sandbox)
    n = 0
    for st in JuliaSyntax.children(tree)
        try
            JuliaLowering.lower(mod, st)
            n += 1
        catch e
            e isa StackOverflowError && rethrow()
        end
    end
    return n
end

const files = ["base/range.jl", "base/abstractarray.jl", "base/strings/string.jl"]
const root = joinpath(Sys.BINDIR, "..", "..")

for f in files
    text = read(joinpath(root, f), String)
    tree = parsefile(text, f)
    n = lower_all(tree) # warm up compilation
    ts = Float64[]
    for _ in 1:15
        tree = parsefile(text, f)
        GC.gc()
        push!(ts, @elapsed lower_all(tree))
    end
    sort!(ts)
    println(rpad(f, 28), " stmts=", lpad(n, 4),
            "  min=", round(ts[1] * 1000; digits=2), "ms",
            "  median=", round(ts[8] * 1000; digits=2), "ms")
end
