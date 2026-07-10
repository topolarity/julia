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
        # From PkgEval: SuperEnum v0.0.4, test/runtests.jl:4-11 (eval of @macroexpand'd @superenum module)
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

end
