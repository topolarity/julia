@testset "hooks" begin
    test_mod = Module()

    @testset "`core_lowering_hook`" begin
        # Non-AST types are often sent through lowering
        stuff = Any[LineNumberNode(1), 123, 123.123, true, "foo", test_mod]
        for s in stuff
            @test JL.core_lowering_hook(s, test_mod) == Core.svec(s)
        end

        for ast_type in (Expr, JL.SyntaxTree)
            ex = parsestmt(ast_type, "[1,2,3] .+= 1")
            out = JL.core_lowering_hook(ex, test_mod)
            @test out isa Core.SimpleVector && out[1] isa Expr
            val = Core.eval(test_mod, out[1])
            @test val == [2,3,4]
        end

        # file argument mismatch with embedded linenumbernodes shouldn't crash
        ex = Expr(:block, LineNumberNode(111), :(x = 1), LineNumberNode(222), :(x + 1))
        lwr = JuliaLowering.core_lowering_hook(ex, test_mod, "foo.jl", 333)[1]
        @test Core.eval(test_mod, lwr) === 2
    end

    function jeval(str)
        prog = parseall(Expr, str)
        try
            JL.activate!()
            return Core.eval(test_mod, prog)
        finally
            JL.activate!(false)
        end
    end
    @testset "integration: `JuliaLowering.activate!`" begin
        out = jeval("global asdf = 1")
        @test out === 1
        @test isdefined(test_mod, :asdf)

        out = jeval("module M; x = 1; end")
        @test out isa Module
        @test isdefined(test_mod, :M)
        @test isdefined(test_mod.M, :x)

        @test jeval("@ccall jl_value_ptr(nothing::Any)::Ptr{Cvoid}") isa Ptr{Cvoid}

        # Tricky cases with symbols
        out = jeval("""module M2
                Base.@constprop :aggressive function f(x); x; end
                const what = ccall(:jl_value_ptr, Ptr{Cvoid}, (Any,), Core.nothing)
            end""")
        @test out isa Module
        @test isdefined(test_mod, :M2)
        @test isdefined(test_mod.M2, :f)
        @test isdefined(test_mod.M2, :what)

        out = jeval(""" "docstring" module M3 end """)
        @test out isa Module
        @test isdefined(test_mod, :M3)

        # Macros may produce toplevel expressions.  Note that julia handles
        # this case badly (macro expansion replaces M5_inner with a
        # globalref) and we handle esc(:M5_inner) badly
        out = jeval("""module M5
            macro newmod()
                return quote
                    let a = 1
                        $(Expr(:toplevel,
                               Expr(:module, true, :M5_inner,
                                    Expr(:block, :(global asdf = 1)))))
                    end
                end
            end
            @newmod()
            end""")
        @test out isa Module
        @test isdefined(test_mod, :M5)
        @test isdefined(test_mod.M5, :M5_inner)
        @test isdefined(test_mod.M5.M5_inner, :asdf)

        @test jeval("Base.@propagate_inbounds @inline meta_double_quote_issue(x) = x") isa Function
    end

    @testset "error log attachments are truncated" begin
        # Regression test: `core_lowering_hook`'s `@info` on a caught
        # exception used to render `code`/`st0`/`st1` unboundedly.  A large
        # (but not otherwise unusual) input can make that dump many MB in
        # size, which blows past log size caps used by CI tooling (e.g.
        # PkgEval's 1MB per-test log limit) and can bury or truncate the
        # actual exception.  Attachments must be capped to a reasonable size
        # instead.
        function deep_binary_expr(n)
            e = :(1 + 1)
            for i in 1:n
                e = :($e + $e)
            end
            e
        end
        # `Expr(:&, ...)` is invalid syntax outside a `ccall` argument list,
        # so this deterministically throws a `LoweringError` in
        # `core_lowering_hook`, with `deep_binary_expr(9)` (~1000s of nodes)
        # attached as (part of) `code`/`st0`/`st1`.
        ex = Expr(:block, Expr(:&, deep_binary_expr(9)))

        io = IOBuffer()
        logger = Base.CoreLogging.SimpleLogger(io)
        Base.CoreLogging.with_logger(logger) do
            @test_throws JL.LoweringError JL.core_lowering_hook(ex, test_mod)
        end
        logtext = String(take!(io))

        # The triage marker used to grep for these errors must survive.
        @test occursin("JuliaLowering threw given input", logtext)
        # Each oversized attachment should show a truncation marker...
        @test occursin("truncated", logtext)
        # ...and the overall log must stay small, regardless of how deep the
        # input expression is.
        @test sizeof(logtext) < 64_000
    end

    @testset "flisp-compat lowering errors (`@eval` path)" begin
        # A user-facing lowering error (here: reading all-underscore `_`) must
        # surface as an ordinary `ErrorException` through the `@eval` path --
        # matching flisp, where `@eval` is `Core.eval` and lowering errors are
        # `ErrorException`. `LoweringError <: Exception` but not `<:
        # ErrorException`, which silently breaks the ubiquitous
        # `@test_throws ErrorException @eval(bad)` idiom (found via DataPipes).
        bad = parsestmt(JL.SyntaxTree, "_.values")

        # `eval_flisp_compat` (what `@eval` expands to) converts to ErrorException
        @test_throws ErrorException JL.eval_flisp_compat(test_mod, bad)
        @test_throws "all-underscore" JL.eval_flisp_compat(test_mod, bad)

        # ...but the programmatic API keeps raising the richer `LoweringError`,
        # as the rest of this suite relies on.
        @test_throws JL.LoweringError JL.eval(test_mod, bad)
        @test_throws JL.LoweringError JL.include_string(test_mod, "_.values")

        # Valid code is unaffected (value returned, no conversion).
        @test JL.eval_flisp_compat(test_mod, parsestmt(JL.SyntaxTree, "1 + 2")) == 3

        # Non-`LoweringError` exceptions (e.g. ordinary runtime errors) pass
        # through unchanged -- only user-facing lowering errors are converted.
        @test_throws DomainError JL.eval_flisp_compat(test_mod, parsestmt(JL.SyntaxTree, "sqrt(-1.0)"))

        # End-to-end through the actual `@eval` macro under an active lowerer.
        prog = parseall(Expr, "try; @eval(_.values); false; catch e; e isa ErrorException; end")
        try
            JL.activate!()
            @test Core.eval(test_mod, prog) === true
        finally
            JL.activate!(false)
        end
    end

    @testset "flisp-compat macro-expansion errors (`LoadError`)" begin
        # A macro that throws while being *expanded* must surface as a
        # `LoadError` through the top-level-eval boundary, matching flisp
        # (`jl_invoke_julia_macro`'s `throw_load_error`). `LoweringError`/
        # `MacroExpansionError` are `<: Exception` but not `<: LoadError`, so
        # the standard `@test_throws LoadError @eval @somemacro(bad)` idiom
        # silently stops matching (found via StationXML / StrLiterals).
        mac_mod = Module(:MacTM)
        Core.eval(mac_mod, :(macro boom(x); x == 0 && error("bad x"); :(nothing); end))
        bad = parsestmt(JL.SyntaxTree, "@boom(0)")

        # `eval_flisp_compat` (the `@eval` path) wraps in `LoadError`...
        err = try; JL.eval_flisp_compat(mac_mod, bad); catch e; e; end
        @test err isa LoadError
        # ...wrapping the macro body's *original* thrown exception directly, as
        # flisp's `jl_invoke_julia_macro` does (`LoadError.error` is the raw
        # cause, not JuliaLowering's `MacroExpansionError` wrapper), so packages
        # that assert the type/message/fields of `ex.error` keep working (found
        # via Match.jl in PkgEval; refines `0fb6078059`).
        @test err.error isa ErrorException
        @test err.error.msg == "bad x"

        # The programmatic API keeps raising the raw `MacroExpansionError`
        # (`JuliaLowering.macroexpand` introspection likewise -- both bypass
        # the flisp-compat boundary, matching flisp's `throw_load_error=0`).
        @test_throws JL.MacroExpansionError JL.eval(mac_mod, bad)
        @test_throws JL.MacroExpansionError JL.include_string(mac_mod, "@boom(0)")
        @test_throws JL.MacroExpansionError JL.macroexpand(mac_mod, bad)

        # `core_lowering_hook` (the `Core.eval`/`include` path) wraps too, and
        # does *not* emit the triage log for these user/package errors.
        io = IOBuffer()
        Base.CoreLogging.with_logger(Base.CoreLogging.SimpleLogger(io)) do
            hookerr = try
                JL.core_lowering_hook(Expr(:macrocall, GlobalRef(mac_mod, Symbol("@boom")),
                                           LineNumberNode(1, :none), 0), mac_mod)
                nothing
            catch e; e; end
            @test hookerr isa LoadError
            @test hookerr.error isa ErrorException
            @test hookerr.error.msg == "bad x"
        end
        @test !occursin("JuliaLowering threw given input", String(take!(io)))

        # The wrapped error matches flisp's shape exactly (inner type + message),
        # for both a plain macro-body error and a *nested* macro-in-macro error
        # (a macro whose expansion produces another macro that throws) -- flisp
        # yields a single `LoadError` holding the innermost original exception in
        # both cases (oracle: `usr/bin/julia` default lowering).
        Core.eval(mac_mod, :(macro typed(); throw(ArgumentError("typed bad")); end))
        terr = try; JL.eval_flisp_compat(mac_mod, parsestmt(JL.SyntaxTree, "@typed()")); catch e; e; end
        @test terr isa LoadError
        @test terr.error isa ArgumentError
        @test terr.error.msg == "typed bad"

        Core.eval(mac_mod, :(macro inner(); error("inner boom"); end))
        Core.eval(mac_mod, :(macro outer(); :(@inner()); end))
        nerr = try; JL.eval_flisp_compat(mac_mod, parsestmt(JL.SyntaxTree, "@outer()")); catch e; e; end
        @test nerr isa LoadError
        @test nerr.error isa ErrorException      # innermost cause, not a nested MacroExpansionError
        @test nerr.error.msg == "inner boom"

        # End-to-end `@eval @boom(0)` under an active lowerer -> LoadError.
        Core.eval(test_mod, :(macro boom(x); x == 0 && error("bad x"); :(nothing); end))
        prog = parseall(Expr, "try; @eval(@boom(0)); false; catch e; e isa LoadError; end")
        try
            JL.activate!()
            @test Core.eval(test_mod, prog) === true
        finally
            JL.activate!(false)
        end
    end
end
