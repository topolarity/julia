# Scaffolding for the pure/staged-context test below: a `@generated` function
# must be defined at module scope. Its generator deliberately fails lowering
# (an unlabeled `break` outside any loop) while the runtime holds
# `in_pure_callback == 1` (staging), and invokes the hook under a captured
# logger so the test can assert the triage `@info` is suppressed there.
const _pure_ctx_log = IOBuffer()
@generated function _staged_lowering_probe(::Val{N}) where {N}
    bad = Expr(:lambda, Any[Symbol("#self#"), :x],
               Expr(:block, Expr(:break), Expr(:return, 1)))
    Base.CoreLogging.with_logger(Base.CoreLogging.SimpleLogger(_pure_ctx_log)) do
        try
            JuliaLowering.core_lowering_hook(bad, @__MODULE__)
        catch
        end
    end
    return :(nothing)
end

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

    @testset "macroexpand-then-eval of a macro-generated `module`" begin
        # A macro returning `Expr(:toplevel, Expr(:module, ...))` (the "macro
        # defines a module" idiom -- EnumX's `@enumx`, SuperEnum's `@superenum`)
        # that is `@macroexpand`ed into a captured value and then `eval`ed
        # *separately* (SuperEnum's own test idiom). `@macroexpand` uses the
        # flisp macro expander, which serializes the module through a
        # `hygienic-scope` wrapper; the C toplevel driver peels the enclosing
        # `:toplevel` and hands that wrapper to `core_lowering_hook` alone, so
        # after macro/hygiene expansion the form surfaces as a bare top-level
        # `module`. It must still be recognized as top-level -- this used to fail
        # with "`module` is only allowed at top level" (evaluating the same macro
        # call inline always worked; only the macroexpand-then-eval path broke).
        out = jeval("""
            module MkModHome
                const SECRET = 41
                macro mkmod(name)
                    blk = quote
                        module \$(esc(name))
                            const \$(esc(:got)) = SECRET + 1  # RHS unescaped -> macro home
                        end
                        const \$(esc(:trailing)) = 7          # trailing toplevel stmt
                    end
                    blk.head = :toplevel
                    return blk
                end
            end
            expr = @macroexpand MkModHome.@mkmod EnumMod
            @assert expr.head == :toplevel
            Core.eval(@__MODULE__, expr)
            (EnumMod.got, trailing)
        """)
        # module created, its body evaluated (escaped `got` binds in `EnumMod`),
        # unescaped `SECRET` resolves back to the macro's home module
        # (`MkModHome`, giving 42, i.e. hygiene preserved), and the toplevel
        # statement trailing the module also runs.
        @test out == (42, 7)
        @test isdefined(test_mod, :EnumMod)
        @test isdefined(test_mod.EnumMod, :got)

        # The same captured expression `eval`ed a second time re-runs cleanly
        # (no template-mutation hazard from the first lowering).
        out2 = jeval("""
            module MkModHome2
                macro mkmod(name)
                    blk = quote
                        module \$(esc(name))
                            const \$(esc(:w)) = 7
                        end
                    end
                    blk.head = :toplevel
                    return blk
                end
            end
            expr = @macroexpand MkModHome2.@mkmod TwiceMod
            Core.eval(@__MODULE__, expr)
            r1 = TwiceMod.w
            Core.eval(@__MODULE__, expr)
            (r1, TwiceMod.w)
        """)
        @test out2 == (7, 7)
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
        # `Expr(:&, ...)` is invalid syntax outside a `ccall` argument list, so
        # this deterministically throws a (non-internal) lowering error in
        # `core_lowering_hook`, with `deep_binary_expr(9)` (~1000s of nodes)
        # attached as (part of) `code`/`st0`/`st1`. The hook converts non-internal
        # lowering errors to `ErrorException` (flisp-compat, see the
        # `core_lowering_hook` path testset below); the triage log still fires
        # first, which is what this test exercises.
        ex = Expr(:block, Expr(:&, deep_binary_expr(9)))

        io = IOBuffer()
        logger = Base.CoreLogging.SimpleLogger(io)
        Base.CoreLogging.with_logger(logger) do
            @test_throws ErrorException JL.core_lowering_hook(ex, test_mod)
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

    @testset "triage `@info` is suppressed inside pure/staged lowering" begin
        # When lowering fails inside a `@generated` function's staging (or any
        # pure callback), `core_lowering_hook`'s diagnostic `@info` must NOT
        # run: its blocking write would hit "task switch not allowed from inside
        # staged nor pure functions" under log-pipe backpressure (seen via
        # PlanningDomains -> PDDL -> ValSplit), masking the real, catchable
        # lowering error. Here `_staged_lowering_probe`'s generator fails
        # lowering while `in_pure_callback == 1`; the captured logger must stay
        # free of the triage marker. (The non-pure path above still logs it.)
        take!(_pure_ctx_log)
        _staged_lowering_probe(Val(1))
        @test !occursin("JuliaLowering threw given input",
                        String(take!(_pure_ctx_log)))
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

    @testset "(AI) flisp-compat lowering errors (`core_lowering_hook` path)" begin
        # The `Core._lower` hook underlying plain `eval`/`include`/toplevel code
        # must apply the *same* non-internal `LoweringError` -> `ErrorException`
        # conversion as the `@eval` path above, so `@test_throws ErrorException
        # eval(bad)` keeps matching (found via Chain, whose `@chain begin _ end`
        # lowers to a read of an all-underscore temp). `LoweringError <: Exception`
        # but not `<: ErrorException`.
        io = IOBuffer()
        hookerr = Base.CoreLogging.with_logger(Base.CoreLogging.SimpleLogger(io)) do
            try
                JL.core_lowering_hook(parsestmt(JL.SyntaxTree, "local x = _"), test_mod)
                nothing
            catch e; e; end
        end
        @test hookerr isa ErrorException
        @test occursin("all-underscore", hookerr.msg)
        # ...and, unlike the `MacroExpansionError` branch, the triage log MUST
        # still fire for these: PkgEval both-fail sweeps grep this marker to
        # classify equivalent failures, so the conversion runs *after* logging.
        @test occursin("JuliaLowering threw given input", String(take!(io)))

        # An `internal` (assertion-class) `LoweringError` stays loud and
        # propagates unconverted through the hook. `const (a, b) = c = (1, 2)`
        # currently trips an internal lowering error (see the `@test_broken` in
        # test/assignments.jl); if that path is ever fixed, pick another
        # internal-error trigger here.
        io2 = IOBuffer()
        ierr = Base.CoreLogging.with_logger(Base.CoreLogging.SimpleLogger(io2)) do
            try
                JL.core_lowering_hook(parsestmt(Expr, "const (hk_a, hk_b) = hk_c = (1, 2)"), test_mod)
                nothing
            catch e; e; end
        end
        @test ierr isa JL.LoweringError
        @test ierr.internal === true

        # The programmatic API keeps raising the richer `LoweringError` unchanged
        # (the rest of this suite relies on that).
        @test_throws JL.LoweringError JL.eval(test_mod, parsestmt(JL.SyntaxTree, "local x = _"))
        @test_throws JL.LoweringError JL.include_string(test_mod, "local x = _")

        # End-to-end through the real `Core.eval` toplevel path under an active
        # lowerer (Chain's exact `eval(quote ... end)` shape): the ubiquitous
        # `@test_throws ErrorException eval(bad)` idiom now matches.
        try
            JL.activate!()
            @test_throws ErrorException Core.eval(test_mod, :(local ex_u = _))
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

    @testset "`LoadError` conversion failure cannot mask the original error" begin
        # The `MacroExpansionError` -> `LoadError` conversion above is
        # diagnostic shaping on an exception-reporting path: if it ever throws
        # (believed total today, but future edits could regress that), the
        # user's original error must surface, not the conversion's own
        # exception (cf. the ForwardMethods triage, where an opaque error at
        # the conversion's throw site was initially mistaken for exactly such
        # masking). `_macroexpansion_loaderror_total` guarantees this; the
        # conversion failure is injected via its test-only `convert_exc` hook.
        mm = Module()
        Core.eval(mm, :(macro boomc(); error("original cause"); end))
        exc = try
            JL.eval(mm, parsestmt(JL.SyntaxTree, "@boomc()"))
            nothing
        catch e
            e
        end
        @test exc isa JL.MacroExpansionError
        lnn = LineNumberNode(1, :none)
        # the normal conversion result is unchanged
        le = JL._macroexpansion_loaderror_total(exc, lnn)
        @test le isa LoadError
        @test le.error isa ErrorException && le.error.msg == "original cause"
        # a broken conversion yields the original exception, unmasked
        broken_convert = (e, fb) -> error("conversion machinery broke")
        @test JL._macroexpansion_loaderror_total(exc, lnn, broken_convert) === exc
    end

    @testset "(AI) named-tuple message parity + `syntax:` prefix" begin
        # Found via AtBackslash v0.1.0 in a PkgEval comparison against flisp
        # lowering. Its `@\` macro emits a named tuple with a call element
        # (`Expr(:tuple, Expr(:parameters, :(f(x))))`), and its test asserts
        # flisp's exact message `syntax: invalid named tuple element "f(x)"` is a
        # substring of `sprint(showerror, err)`. JuliaLowering both rejected the
        # shape (behavioral parity held) *and* worded it differently
        # ("expected identifier, `=`, or `...` after semicolon", no `syntax:`
        # prefix), so only the message diverged.
        #
        # flisp surfaces every lowering error's `Expr(:error, msg)` sentinel as
        # `syntax: <msg>` (`src/toplevel.c`); the flisp-compat boundaries
        # (`eval_flisp_compat` / `core_lowering_hook`) mirror that prefix, and the
        # named-tuple element/field-name/duplicate messages are worded like flisp
        # with the offending subtree deparsed and interpolated.

        # The exact AtBackslash reproduction: the `@\` macro's `Expr` output.
        atbackslash_shape = Expr(:tuple, Expr(:parameters, :(f(x))))
        err = try; JL.eval_flisp_compat(test_mod, atbackslash_shape); catch e; e; end
        @test err isa ErrorException
        @test occursin("syntax: invalid named tuple element \"f(x)\"", err.msg)

        # Named-tuple message family (surface syntax; via the flisp-compat
        # boundary, so the `syntax:` prefix is included), each matching flisp.
        nt_cases = [
            "(; f(x))"     => "syntax: invalid named tuple element \"f(x)\"",
            "(; 1)"        => "syntax: invalid named tuple element \"1\"",
            "(; f(x)=1)"   => "syntax: invalid named tuple field name \"f(x)\"",
            "(; a[]=1)"    => "syntax: invalid named tuple field name \"a[]\"",
            "(; a=1, a=2)" => "syntax: field name \"a\" repeated in named tuple",
        ]
        for (src, msg) in nt_cases
            e = try; JL.eval_flisp_compat(test_mod, parsestmt(JL.SyntaxTree, src)); catch e; e; end
            @test e isa ErrorException
            @test e.msg == msg
        end

        # Regression guard: keyword-argument calls share the underlying
        # validation/desugaring but flisp words them differently; those messages
        # are intentionally left unchanged (only the `syntax:` prefix is added).
        # They must NOT pick up the named-tuple wording.
        for src in ("f(; g(x))", "f(; a=1, a=2)")
            e = try; JL.eval_flisp_compat(test_mod, parsestmt(JL.SyntaxTree, src)); catch e; e; end
            @test e isa ErrorException
            @test !occursin("named tuple", e.msg)
        end
    end
end
