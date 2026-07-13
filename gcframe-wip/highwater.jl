# Whole-pipeline stack high-water: smallest Task stack that can lower
# base/range.jl end-to-end, found by bisection.
using JuliaLowering
using JuliaLowering: JuliaSyntax

const text = read(joinpath(Sys.BINDIR, "..", "..", "base", "range.jl"), String)

function lower_file()
    stream = JuliaSyntax.ParseStream(text)
    JuliaSyntax.parse!(stream; rule=:all)
    tree = JuliaSyntax.build_tree(JuliaSyntax.SyntaxTree, stream; filename="range.jl")
    mod = Module(:Sandbox)
    n = 0
    for st in JuliaSyntax.children(tree)
        try
            JuliaLowering.lower(mod, st)
            n += 1
        catch e
            e isa StackOverflowError && rethrow()
            # non-stack lowering errors (undefined macros etc.) don't matter here
        end
    end
    return n
end

function fits(stacksize)
    ok = Ref(false)
    t = Task(() -> (lower_file(); ok[] = true), stacksize)
    schedule(t)
    try
        wait(t)
    catch
    end
    return ok[]
end

println("statements lowered ok: ", lower_file())

lo, hi = 16 * 1024, 4 * 1024 * 1024
@assert fits(hi)
while hi - lo > 4096
    mid = (lo + hi) ÷ 2
    if fits(mid)
        global hi = mid
    else
        global lo = mid
    end
end
println("stack high-water for lowering base/range.jl: ~", hi ÷ 1024, " KiB")
