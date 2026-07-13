# Reproduce the exact @invokelatest body under fresh JIT compilation.
src = join(readlines(joinpath(Sys.BINDIR, "..", "..", "base", "reflection.jl"))[1405:1447], "\n")
src = replace(src, "macro invokelatest(ex)" => "macro myinvokelatest(ex)")
modsrc = "module M\nusing Base: isexpr, destructure_callex, _topmod, invokelatest, invokelatest_gr\n" * src * "\nend"
Core.eval(Main, Meta.parseall(modsrc))

const lg = Base.CoreLogging.logging_error
for i in 1:5
    ex = Expr(:macrocall, GlobalRef(M, Symbol("@myinvokelatest")), LineNumberNode(1, :here),
              Expr(:call, lg, 1, 2, 3, 4, 5, 6, 7, 8, true))
    try
        out = macroexpand(Main, ex)
        println("run $i: ok  (", typeof(out), ")")
    catch e
        println("run $i: THREW ", typeof(e), ": ", sprint(showerror, e)[1:min(end,120)])
    end
end
