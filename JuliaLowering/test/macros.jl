test_mod = @newmod(macro_test)
@eval test_mod import JuliaLowering
Base.eval(test_mod, :(const var"@ast" = $(JuliaLowering.var"@ast")))

# Set up identity macros for use in this file
# - `old_e`, escaping its whole output, should do nothing to an expression
# - `new_m`, introducing no new syntax, should behave exactly as `old_e` does
# - `old_*` should behave the same across JL and flisp
# - `old_h` should not be specified too hard here (buggy renaming pass)
fl_eval(test_mod, :(macro old_e(x); esc(x); end))
fl_eval(test_mod, :(macro old_h(x); x; end))
JuliaLowering.include_string(test_mod, "macro new_m(x); x; end")
fl_eval(test_mod, :(global mvar = "global mvar"))

@testset "syntax versioning sanity-check" begin
    @test JuliaLowering.include_string(
        test_mod, "JuliaLowering.@syntax_version") ==
        JuliaSyntax.JL_NEW_SYNTAX_VERSION
    @test JuliaLowering.include_string(
        test_mod, "JuliaLowering.@syntax_version"; expr_compat_mode=false) ==
        JuliaSyntax.JL_NEW_SYNTAX_VERSION
    @test JuliaLowering.include_string(
        test_mod, "JuliaLowering.@syntax_version"; expr_compat_mode=true) ==
        JuliaSyntax.JL_OLD_SYNTAX_VERSION
end

# Basic checks that arbitrary nesting of transparent macros (no new syntax in new
# macros, escaped/unhygienic in old macros) doesn't introduce opaque layers
@testset "basic transparent macros: old macros" for run in [
    (x::String)->Base.include_string(
        test_mod, "#=FLISP SANITY-CHECK=# "*x),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    @test run("@old_e let mvar = 0; mvar; end") == 0
    @test run("@old_e let @old_e(mvar = 0); mvar; end") == 0
    @test run("@old_e let @old_e(@old_e(mvar = 0)); mvar; end") == 0
    @test run("@old_e let @old_e(mvar) = 0; mvar; end") == 0
    @test run("@old_e let @old_e(@old_e(mvar)) = 0; mvar; end") == 0
    @test run("@old_e let mvar = 0; @old_e(mvar); end") == 0
    @test run("@old_e let mvar = 0; @old_e(@old_e(mvar)); end") == 0
    @test run("@old_e let @old_e(@old_e(mvar) = 0); @old_e(mvar); end") == 0

    @test run("@old_h let mvar = 0; mvar; end") == 0
    @test run("@old_h let @old_e(mvar = 0); mvar; end") == 0
    @test run("@old_h let @old_e(@old_e(mvar = 0)); mvar; end") == 0
    @test run("@old_h let @old_e(mvar) = 0; mvar; end") == 0
    @test run("@old_h let @old_e(@old_e(mvar)) = 0; mvar; end") == 0
    @test run("@old_h let mvar = 0; @old_e(mvar); end") == 0
    @test run("@old_h let mvar = 0; @old_e(@old_e(mvar)); end") == 0
    @test run("@old_h let @old_e(@old_e(mvar) = 0); @old_e(mvar); end") == 0

    @test run("@old_h @old_h let mvar = 0; mvar; end") == 0
    @test run("@old_h @old_h let @old_e(mvar = 0); mvar; end") == 0
    @test run("@old_h @old_h let @old_e(@old_e(mvar = 0)); mvar; end") == 0
    @test run("@old_h @old_h let @old_e(mvar) = 0; mvar; end") == 0
    @test run("@old_h @old_h let @old_e(@old_e(mvar)) = 0; mvar; end") == 0
    @test run("@old_h @old_h let mvar = 0; @old_e(mvar); end") == 0
    @test run("@old_h @old_h let mvar = 0; @old_e(@old_e(mvar)); end") == 0
    @test run("@old_h @old_h let @old_e(@old_e(mvar) = 0); @old_e(mvar); end") == 0
end
@testset "basic transparent macros: new macros only" for expr_compat_mode in [true, false]
    local run = (x::String)->JuliaLowering.include_string(test_mod, x; expr_compat_mode)

    @test run("@new_m let mvar = 0; mvar; end") == 0
    @test run("@new_m let @new_m(mvar = 0); mvar; end") == 0
    @test run("@new_m let @new_m(@new_m(mvar = 0)); mvar; end") == 0
    @test run("@new_m let @new_m(mvar) = 0; mvar; end") == 0
    @test run("@new_m let @new_m(@new_m(mvar)) = 0; mvar; end") == 0
    @test run("@new_m let mvar = 0; @new_m(mvar); end") == 0
    @test run("@new_m let mvar = 0; @new_m(@new_m(mvar)); end") == 0
    @test run("@new_m let @new_m(@new_m(mvar) = 0); @new_m(mvar); end") == 0
end
@testset "basic transparent macros: new+old interop" for expr_compat_mode in [true, false],
    mcall in ["@old_e ", "@new_m ", "@old_e @new_m ", "@new_m @old_e "],
    old_h in ["", "@old_h "]

    local run = (x::String)->JuliaLowering.include_string(test_mod, x; expr_compat_mode)

    @test run(old_h*mcall*"let mvar = 0; mvar; end") == 0
    @test run(old_h*"let ("*mcall*"mvar = 0); mvar; end") == 0
    @test run(old_h*"let ("*mcall*"mvar) = 0; mvar; end") == 0
    @test run(old_h*"let mvar = 0; ("*mcall*"mvar); end") == 0

    @testset for mcall2 in ["@old_e ", "@new_m ", "@old_e @new_m ", "@new_m @old_e "]
        @test run(old_h*mcall*"let ("*mcall2*"mvar) = 0; mvar; end") == 0
        @test run(old_h*mcall*"let mvar = 0; ("*mcall2*"mvar); end") == 0
        @test run(old_h*"let ("*mcall*"mvar = 0); ("*mcall2*"mvar); end") == 0
    end
end

# More simple checks with no difference between macro module and macrocall module
isdefined(test_mod, :x) && Base.delete_binding(test_mod, :x)
fl_eval(test_mod, :(macro old_read_x(); :x; end))
fl_eval(test_mod, :(macro old_suggest_x(arg)
                        quote
                            let x = "suggested (old)"
                                $(esc(arg))
                            end
                        end
                    end))
JuliaLowering.include_string(test_mod, raw"""
    macro new_read_x(); @legacy_quote_to_syntax :x; end
""")
JuliaLowering.include_string(test_mod, raw"""
    macro new_suggest_x(arg)
        @legacy_quote_to_syntax quote
            let x = "suggested (new)"
                $arg
            end
        end
    end
""")
@testset "basic hygiene: check that name resolution fails where it should (flisp)"  for run in [
    (x::String)->fl_eval(test_mod,JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]
    @test_throws UndefVarError run("@old_read_x()")
    @test_throws UndefVarError run("let x = 0; @old_read_x(); end")
    @test_throws UndefVarError run("@old_suggest_x(x)")
    @test_throws UndefVarError run("@old_suggest_x(@old_read_x())")
    @test run("let x = 1; @old_suggest_x(x); end") == 1
    @test run("@old_suggest_x(let x = 1; x; end)") == 1
    @test_throws UndefVarError run("@old_suggest_x(let x = 1; @old_read_x(); end)") == 1
end
@testset "basic hygiene: check that name resolution fails where it should (new)" for run in [
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    @test_throws UndefVarError run("@new_read_x()")
    @test_throws UndefVarError run("let x = 0; @new_read_x(); end")
    @test_throws UndefVarError run("@new_suggest_x(x)")
    @test_throws UndefVarError run("@new_suggest_x(@new_read_x())")
    @test run("let x = 1; @new_suggest_x(x); end") == 1
    @test run("@new_suggest_x(let x = 1; x; end)") == 1
    @test_throws UndefVarError run("@new_suggest_x(let x = 1; @new_read_x(); end)") == 1

    @testset "old/new interop" begin
        @testset for wrapper in ["", "@old_e ", "@old_h ", "@new_m "]
            @test_throws UndefVarError run(wrapper*"@old_suggest_x(@new_read_x())")
            @test_throws UndefVarError run(wrapper*"@new_suggest_x(@old_read_x())")
            @test run(wrapper*"let x = 1; @old_suggest_x(x); end") == 1
            @test run(wrapper*"let x = 1; @new_suggest_x(x); end") == 1
            @test run(wrapper*"@old_suggest_x(let x = 1; x; end)") == 1
            @test run(wrapper*"@new_suggest_x(let x = 1; x; end)") == 1
        end
    end
end

@eval test_mod (global test_mod_global = "test_mod_global")
@newmod(EvalMod, test_mod)
@testset "@eval" for run in [
    (x::String)->fl_eval(test_mod,JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    has_syntax = run(raw"@legacy_quote_to_syntax :x") isa SyntaxTree
    treetype = has_syntax ? SyntaxTree : Expr
    symtype = has_syntax ? SyntaxTree : Symbol
    valtype = has_syntax ? SyntaxTree : Any

    @test run(raw"@eval nothing") == nothing
    @test run(raw"@eval :sym") == :sym
    @test run(raw"@eval QuoteNode(:sym)") == QuoteNode(:sym)
    @test run(raw"@eval Expr(:call, :identity, 1)") == Expr(:call, :identity, 1)
    @test run(raw"@eval :(identity(1))") == Expr(:call, :identity, 1)
    # syntax version of the caller should be propagated to JL.eval
    @test run(raw"@eval @legacy_quote_to_syntax(:sym)") isa symtype
    @test run(raw"@eval @legacy_quote_to_syntax(:(identity(1)))") isa treetype
    @test run(raw"@eval @eval @legacy_quote_to_syntax(:(identity(1)))") isa treetype

    # quoting behaves the same as outside of eval
    @test run(raw"@eval(:(1 + 2))") == Expr(:call, :+, 1, 2)
    @test run(raw"@eval(:true)") == true
    @test run(raw"@eval(:x)") == :x

    # interpolation
    @test run(raw"let x = nothing; @eval $x; end") == nothing
    @test run(raw"let x = :identity; @eval $x; end") == Base.identity
    @test run(raw"let x = QuoteNode(:sym); @eval $x; end") == :sym
    @test run(raw"let x = Expr(:call, :identity, 1); @eval $x; end") == 1
    @test run(raw"let x = :(identity(1)); @eval $x; end") == 1
    @test run(raw"let x = @legacy_quote_to_syntax(:identity); @eval $x; end") == Base.identity
    @test run(raw"let x = @legacy_quote_to_syntax(:(identity(1))); @eval $x; end") == 1

    # interpolate into quote
    @test run(raw"let test_mod_global = 0xbad
        @eval (@legacy_quote_to_syntax :($test_mod_global))
    end") isa valtype
    @test run(raw"let test_mod_global = 0xbad
        @eval @legacy_quote_to_syntax(:(1,$test_mod_global))
    end") isa treetype

    # interpolate into quote, double-unquote (mixes of syntax and expr may not
    # need to work)
    @test run(raw"let x = @legacy_quote_to_syntax(:identity)
        @eval (:($($x)))
    end") == Base.identity
    @test run(raw"let x = @legacy_quote_to_syntax(:identity)
        @eval (@legacy_quote_to_syntax :($($x)))
    end") isa valtype
    @test run(raw"let x = @legacy_quote_to_syntax(:identity)
        @eval @legacy_quote_to_syntax(:(1,$$x))
    end") isa treetype
    @test run(raw"let x = @legacy_quote_to_syntax(:identity)
        @eval $(@eval (:(1,$$x)))
    end") == (1, Base.identity)

    # module eval-ed into
    @test run(raw"@eval @__MODULE__") == test_mod
    @test run(raw"@eval @eval @__MODULE__") == test_mod
    # two-arg eval should not obey typical hygiene: decls go to specified module
    @test run(raw"@eval EvalMod @__MODULE__") == test_mod.EvalMod
    run(raw"@eval EvalMod global eval_mod_global = 1"); Core.@latestworld
    @test test_mod.EvalMod.eval_mod_global == 1
    run(raw"@eval EvalMod eval_mod_global_implicit = 1"); Core.@latestworld
    @test test_mod.EvalMod.eval_mod_global_implicit == 1
    # standard hygiene atop two-arg eval
    fl_eval(test_mod, :(module MacroMod
                        module MacroModInner; end
                        macro m_setglobal(); esc(:(mmglobal0 = 0)); end
                        macro m_eval_inner(x); :(@eval $MacroModInner $x) ; end
                        end))
    Core.@latestworld
    @eval test_mod.EvalMod (const MacroMod2 = $(test_mod.MacroMod))
    @eval test_mod.EvalMod (const var"@legacy_quote_to_syntax" =
        $(test_mod.var"@legacy_quote_to_syntax"))
    @test run(raw"@eval EvalMod @legacy_quote_to_syntax(:(1 + 1))") isa treetype
    @test run(raw"@eval @eval EvalMod @legacy_quote_to_syntax(:(1 + 1))") isa treetype

    @test run(raw"@eval EvalMod MacroMod2.@m_setglobal") == 0
    Core.@latestworld
    @test isdefined(test_mod.EvalMod, :mmglobal0)
    @test !isdefined(test_mod, :mmglobal0)
    @test !isdefined(test_mod.MacroMod, :mmglobal0)

    @test run(raw"@eval EvalMod MacroMod2.@m_eval_inner(global mmglobal1 = 1)") == 1
    Core.@latestworld
    @test isdefined(test_mod.MacroMod.MacroModInner, :mmglobal1)
    @test !isdefined(test_mod, :mmglobal1)
    @test !isdefined(test_mod.MacroMod, :mmglobal1)
    @test !isdefined(test_mod.EvalMod, :mmglobal1)

    # interpolation into top-level: symbol declared in the new module
    run(raw"let x = @legacy_quote_to_syntax(:sym)
        @eval EvalMod module tmp; module inner_eval_mod; global $x = 123; end; end
    end") isa Module
    Core.@latestworld
    @test test_mod.EvalMod.tmp.inner_eval_mod isa Module
    @test test_mod.EvalMod.tmp.inner_eval_mod.sym == 123

    # hygiene
    run("let eval_result = 0; @eval 1+1; eval_result; end") == 0

    @testset "(AI) single-arg @eval does not over-preserve hygiene" for expr_compat_mode in (true, false)
        root = @newmod(root)
        JuliaLowering.include_string(root, raw"""
        module MacB
            import JuliaLowering.@legacy_quote_to_syntax
            macro do_eval()
                @legacy_quote_to_syntax quote
                    @eval (@__MODULE__)
                end
            end
        end
        module MacA
            import JuliaLowering.@legacy_quote_to_syntax
            import ..MacB
            macro wrap()
                @legacy_quote_to_syntax quote
                    @eval (@__MODULE__)
                end
            end
            macro via_b()
                @legacy_quote_to_syntax quote
                    MacB.@do_eval()
                end
            end
            macro wrap_ee()
                @legacy_quote_to_syntax quote
                    @eval @eval (@__MODULE__)
                end
            end
            macro wrap_two_arg()
                # two-arg control: explicit target module; the payload's
                # `@__MODULE__` must still see the *target* module
                @legacy_quote_to_syntax quote
                    @eval MacB (@__MODULE__)
                end
            end
            macro wrap_arg(ex)
                # caller-provided payload (caller's hygiene layer)
                @legacy_quote_to_syntax quote
                    @eval $ex
                end
            end
            macro wrap_fn()
                # `@eval` captures the module current when the enclosing function
                # *definition* is expanded, like flisp
                @legacy_quote_to_syntax quote
                    () -> @eval (@__MODULE__)
                end
            end
            macro mkmod()
                mod = gensym("EvalMod")
                @legacy_quote_to_syntax quote
                    @eval module $mod
                        const inside = (@__MODULE__)
                    end
                end
            end
            macro mkmod_payload(ex)
                mod = gensym("EvalMod2")
                @legacy_quote_to_syntax quote
                    @eval module $mod
                        $ex
                    end
                end
            end
        end
        module Sub
            import ..MacA
        end
        """; expr_compat_mode)
        Core.@latestworld

        run(str) = JuliaLowering.include_string(root, str; expr_compat_mode)

        # `@eval` inside another macro's unescaped expansion evaluates in the
        # caller's module, not the macro's
        @test run("MacA.@wrap()") === root
        # ... even when the `@eval`-ing macro is called by another macro's expansion
        # (flisp: still the dynamic module, not either macro's module)
        @test run("MacA.@via_b()") === root
        # `@eval` nested in `@eval` re-expands against the outer target
        @test run("MacA.@wrap_ee()") === root
        # two-arg control: explicit module wins; payload `@__MODULE__` follows it
        @test run("MacA.@wrap_two_arg()") === root.MacB
        # macro-generated closure: `@eval` binds the definition-time module
        @test Base.invokelatest(run("MacA.@wrap_fn()")) === root
        # the same macro evaluated into a different module follows the live module
        @test JuliaLowering.include_string(
            root.Sub, "MacA.@wrap()"; expr_compat_mode) === root.Sub

        # Caller-provided payloads evaluate in the caller's module
        @test run("MacA.@wrap_arg(arg_marker = (@__MODULE__))") === root
        if !expr_compat_mode
            # With SyntaxTree-passed arguments the payload keeps the caller's
            # hygiene: the global lands in `root` and is visible there. (In
            # expr_compat_mode the old-style Expr round-trip re-layers the payload
            # with the macro's hygiene and the assignment becomes a hygienic
            # toplevel local -- a pre-existing divergence from flisp tracked by
            # the "hygienic toplevel assignments" TODO in scope_analysis.jl.)
            @test Base.invokelatest(isdefined, root, :arg_marker)
            @test Base.invokelatest(getfield, root, :arg_marker) === root
        end

        # The SafeTestsets shape: a macro-generated `@eval module $mod ... end`
        # creates the module under the dynamic (caller) module
        m = run("MacA.@mkmod()")
        @test m isa Module
        @test parentmodule(m) === root
        @test Base.invokelatest(getfield, m, :inside) === m
        # ... and user payload interpolated into the module body sees the fresh
        # module as its dynamic module (a user's own `@eval` inside a
        # `@safetestset` acts on the anonymous test module)
        m2 = run("MacA.@mkmod_payload(@eval user_marker = (@__MODULE__))")
        @test m2 isa Module
        @test parentmodule(m2) === root
        @test Base.invokelatest(getfield, m2, :user_marker) === m2

        if expr_compat_mode
            # Escaped expansions (old-style macros only): same dynamic target
            JuliaLowering.include_string(root, raw"""
        module MacEsc
            macro wrap_esc()
                esc(quote
                    @eval esc_marker = (@__MODULE__)
                end)
            end
        end
        """; expr_compat_mode)
            Core.@latestworld
            @test run("MacEsc.@wrap_esc()") === root
            @test Base.invokelatest(isdefined, root, :esc_marker)
            @test Base.invokelatest(getfield, root, :esc_marker) === root
        end

        # An old-style (flisp-defined and -lowered) macro whose expansion calls
        # `@eval` gets the same treatment when invoked under JuliaLowering
        fl_eval(root, :(module MacFl
                        macro flwrap()
                            quote
                                @eval (@__MODULE__)
                            end
                        end
                        end))
        Core.@latestworld
        @test run("MacFl.@flwrap()") === root
    end

    @testset "(AI) const shows up in caller mod" begin
        Core.eval(test_mod, :(module MacHome2
                       macro make_const()
                           :( @eval const CMARKER = 42 )
                       end
                       end))
        Core.eval(test_mod, :(MacHome2.@make_const()))
        @test isdefined(test_mod, :CMARKER)

        JuliaLowering.eval(test_mod, :(module MacHome2
                       macro make_const()
                           :( @eval const CMARKER = 42 )
                       end
                       end); expr_compat_mode=true)
        JuliaLowering.eval(test_mod, :(MacHome2.@make_const()))
        @test isdefined(test_mod, :CMARKER)
    end
end

@eval test_mod module hscope_mod; global hscope_g = 123; end
@eval test_mod module nothing_mod; end
@eval test_mod global hscope_g = 234
@testset "hygienic scope should be usable without macros" begin
    @test JuliaLowering.eval(
        test_mod, Expr(
            Symbol("hygienic-scope"),
            1, test_mod); expr_compat_mode=true) == 1
    @test JuliaLowering.eval(
        test_mod, Expr(
            Symbol("hygienic-scope"),
            :hscope_g,
            test_mod.hscope_mod); expr_compat_mode=true) == 123
    @test JuliaLowering.eval(
        test_mod, Expr(
            Symbol("hygienic-scope"),
            Expr(:escape, :hscope_g),
            test_mod.nothing_mod); expr_compat_mode=true) == 234
    @test JuliaLowering.eval(
        test_mod, Expr(
            Symbol("hygienic-scope"), Expr(
                Symbol("hygienic-scope"),
                Expr(:escape, Expr(:escape, :hscope_g)),
                test_mod.nothing_mod),
            test_mod.nothing_mod); expr_compat_mode=true) == 234
    @test JuliaLowering.eval(
        test_mod, Expr(
            Symbol("hygienic-scope"), Expr(
                Symbol("hygienic-scope"),
                Expr(:escape, :hscope_g),
                test_mod.nothing_mod),
            test_mod.hscope_mod); expr_compat_mode=true) == 123
end

Base.eval(test_mod, :(
    test_hscope(x, mod=$test_mod) = Expr(Symbol("hygienic-scope"), x, mod)
))
Base.eval(test_mod, :(
    # +3 new scopes and -4 escapes = normal unhygienic macro
    macro oldstyle_silly_scopes(x, y)
        stmt1 = test_hscope(test_hscope(test_hscope(esc(esc(esc(esc(:($x = 123))))))))
        stmt2 = esc(test_hscope(esc(test_hscope(esc(test_hscope(esc(:($y = 456))))))))
        Expr(:block, stmt1, stmt2)
    end))
@testset "escape and hygienic-scope forms" for run in [
    (x::String)->Base.include_string(
        test_mod, "#=FLISP SANITY-CHECK=# "*x),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    @test run(raw"""
    let (x, y) = (0, 0); @oldstyle_silly_scopes(x, y); (x, y); end
    """) === (123, 456)
    @test run(raw"""begin
    global_x, global_y = 0, 0
    @oldstyle_silly_scopes(global_x, global_y)
    global_x, global_y
    end""") === (123, 456)
end

@testset "apply_expansion_layer mutation testing" begin
    local test_mod = @newmod(apply_expansion_layer)
    # recursion can't stop at module/toplevel/inert without tweaks, because a
    # macro can pull random stuff out of it.  This also tests calling into macro
    # expansion from macros, mostly because re-using macros I've already written
    # is the easiest way to create non-surface-syntax SyntaxTree as of writing.
    JuliaLowering.include_string(test_mod, raw"""
    macro undo_inert(x)
        x2 = JuliaLowering.macroexpand(x)
        x2[1]
    end
    """)
    @test JuliaLowering.include_string(test_mod, raw"""
    let foo = 1; @undo_inert(:foo); end
    """) == 1
    @test JuliaLowering.include_string(test_mod, raw"""
    let foo = 1; @undo_inert(@legacy_quote_to_syntax(:foo)); end
    """) == 1

    JuliaLowering.include_string(test_mod, raw"""
    macro mk_toplevel(x, y, z)
        JuliaSyntax.newnode(
            x._graph, __context__.macrocall, K"toplevel",
            JuliaSyntax.SyntaxList(x, y, z))
    end
    macro toplevel_first_child(x)
        x2 = JuliaLowering.macroexpand(x)
        x2[1]
    end
    """)
    JuliaLowering.include_string(test_mod, raw"""
    macro mk_module(x, y, z)
        @legacy_quote_to_syntax :(module mk_module_mod; $x; $y; $z; end)
    end
    macro module_first_child(x)
        x2 = JuliaLowering.macroexpand(x)
        x2[end][1]
    end
    """)
    # sanity
    @test JuliaLowering.include_string(test_mod, """
    @mk_toplevel(1, :y, "z")
    """) == "z"
    @test JuliaLowering.include_string(test_mod, """
    @mk_module(1, :y, "z")
    """) isa Module
    @test JuliaLowering.include_string(test_mod, """
    let (x, y, z) = (1, :y, "z")
        @toplevel_first_child(@mk_toplevel(x, y, z))
    end
    """) == 1
    @test JuliaLowering.include_string(test_mod, """
    let (x, y, z) = (1, :y, "z")
        @toplevel_first_child(@mk_toplevel(x, y, z))
    end
    """) == 1

    # escape should obey quote/unquote
    JuliaLowering.include_string(test_mod, raw"""
    macro esc_in_quote(); Expr(:quote, Expr(:escape, :x)); end
    """; expr_compat_mode=true)
    @test JuliaLowering.include_string(test_mod, raw"""
    @esc_in_quote
    """; expr_compat_mode=true) == Expr(:escape, :x)
    @test JuliaLowering.include_string(test_mod, raw"""
    @esc_in_quote
    """) == Expr(:escape, :x)

    JuliaLowering.include_string(test_mod, raw"""
    macro esc_in_unquote(); Expr(:quote, Expr(:$, Expr(:escape, :x))); end
    """; expr_compat_mode=true)
    @test JuliaLowering.include_string(test_mod, raw"""
    let x = 1; @esc_in_unquote(); end
    """; expr_compat_mode=true) == 1
    @test JuliaLowering.include_string(test_mod, raw"""
    let x = 1; @esc_in_unquote(); end
    """) == 1
end

JuliaLowering.include_string(test_mod, raw"""
module M
    using ..JuliaLowering: JuliaLowering, adopt_scope, @legacy_quote_to_syntax
    using ..JuliaSyntax

    # Introspection
    macro __MODULE__()
        JuliaLowering.syntax_module(__context__.macrocall)
    end

    macro __FILE__()
        JuliaLowering.filename(__context__.macrocall)
    end

    macro __LINE__()
        JuliaLowering.source_location(__context__.macrocall)[1]
    end

    someglobal = "global in module M"

    # Macro with local variables
    macro foo(ex)
        @legacy_quote_to_syntax :(begin
            x = "`x` from @foo"
            (x, someglobal, $ex)
        end)
    end

    # Set `a_global` in M
    macro set_a_global(val)
        @legacy_quote_to_syntax :(begin
            global a_global = $val
        end)
    end

    macro set_other_global(ex, val)
        @legacy_quote_to_syntax :(begin
            global $ex = $val
        end)
    end

    macro set_global_in_parent(ex)
        sym_ex = @legacy_quote_to_syntax quote; sym_introduced_from_M; end
        e1 = adopt_scope(__context__.macrocall, sym_ex[1])
        @legacy_quote_to_syntax quote
            $e1 = $ex
            nothing
        end
    end

    macro inner()
        @legacy_quote_to_syntax :(y, z)
    end

    macro outer()
        @legacy_quote_to_syntax :((x, @inner))
    end

    macro recursive(N)
        Nval = N.value::Int
        if Nval < 1
            return N
        end
        @legacy_quote_to_syntax quote
            x = $N
            (x, @recursive $(Nval-1))
        end
    end
end
""")

@test JuliaLowering.include_string(test_mod, """
let
    x = "`x` from outer scope"
    M.@foo x
end
""") == ("`x` from @foo", "global in module M", "`x` from outer scope")
@test !isdefined(test_mod.M, :x)


@test JuliaLowering.include_string(test_mod, """
#line1
(M.@__MODULE__(), M.@__FILE__(), M.@__LINE__())
""", "foo.jl") == (test_mod, "foo.jl", 2)

@test !isdefined(test_mod.M, :a_global)
@test JuliaLowering.include_string(test_mod, """
begin
    M.@set_a_global 42
    M.a_global
end
""") == 42

JuliaLowering.include_string(test_mod, """
M.@set_global_in_parent "bent hygiene!"
""")
@test test_mod.sym_introduced_from_M == "bent hygiene!"

JuliaLowering.include_string(test_mod, "M.@set_other_global global_in_test_mod 100")
@test !isdefined(test_mod.M, :global_in_test_mod)
@test test_mod.global_in_test_mod == 100

@test JuliaLowering.include_string(test_mod, """
M.@recursive 3
""") == (3, (2, (1, 0)))

ex = JuliaLowering.parsestmt(JuliaLowering.SyntaxTree, "M.@outer()", filename="foo.jl")
expanded = JuliaLowering.macroexpand(test_mod, ex)
@test JuliaSyntax.sourcetext.(JuliaLowering.flattened_provenance(expanded[2])) == [
    "M.@outer()"
    "@inner"
    "(y, z)"
]

@testset "expansion special case: macrocall in do expression" for expr_compat_mode in [true, false]
    @test JuliaLowering.include_string(test_mod, raw"""
    macro mac_called_in_do_expression(dofunc, arg)
        @legacy_quote_to_syntax :($dofunc($arg))
    end
    """; expr_compat_mode) isa Function
    @test JuliaLowering.include_string(test_mod, raw"""
    @mac_called_in_do_expression(9) do x
        x * 10
    end
    """; expr_compat_mode) == 90
    @test JuliaLowering.include_string(test_mod, raw"""
    let fp = @cfunction(Cint, (Cint,)) do x
            x + Cint(1)
        end
        ccall(fp isa Ptr ? fp : fp.ptr, Cint, (Cint,), 2)
    end
    """; expr_compat_mode) == 3
end

@test JuliaLowering.include_string(test_mod, raw"""
v"1.14"
""") isa VersionNumber
@test JuliaLowering.include_string(test_mod, raw"""
v"1.14"
""";expr_compat_mode=true) isa VersionNumber
@test JuliaLowering.include_string(test_mod, raw"""
Base.Experimental.@VERSION
""") isa NamedTuple
@test JuliaLowering.include_string(test_mod, raw"""
Base.Experimental.@VERSION
""";expr_compat_mode=true) isa NamedTuple

# World age support for macro expansion
JuliaLowering.include_string(test_mod, raw"""
macro world_age_test()
    1
end
""")
world1 = Base.get_world_counter()
JuliaLowering.include_string(test_mod, raw"""
macro world_age_test()
    2
end
""")
world2 = Base.get_world_counter()

call_world_arg_test = JuliaLowering.rebase_layers(JuliaLowering.parsestmt(JuliaLowering.SyntaxTree, "@world_age_test()"), test_mod, JuliaSyntax.JL_NEW_SYNTAX_VERSION)
    @test JuliaLowering.expand_forms_1(call_world_arg_test, world1, true) ≈
        @ast_ 1::K"Value"
    @test JuliaLowering.expand_forms_1(call_world_arg_test, world2, true) ≈
        @ast_ 2::K"Value"

JuliaLowering.include_string(test_mod, """
f_throw(x) = throw(x)
macro m_throw(x)
    :(\$(f_throw(x)))
end
""")
let (err, st) = try
        JuliaLowering.include_string(test_mod, "_never_exist = @m_throw 42")
    catch e
        e, stacktrace(catch_backtrace())
    end
    @test err isa JuliaLowering.MacroExpansionError
    @test !isnothing(err.err)
    # Check that `catch_backtrace` can capture the stacktrace of the macro functions
    @test any(sf->sf.func===:f_throw, st)
    # TODO: store this in DebugInfo
    @test_broken any(sf->sf.func===Symbol("@m_throw"), st)
    @test any(sf->sf.func===Symbol("macro expansion"), st)
end

let err = try
        JuliaLowering.include_string(test_mod, "_never_exist = @m_not_exist 42")
    catch e
        e
    end
    @test err isa JuliaLowering.MacroExpansionError
    @test err.msg == "Macro not found"
    @test err.err isa UndefVarError
end

@test JuliaLowering.include_string(test_mod, "@ccall strlen(\"foo\"::Cstring)::Csize_t") == 3
@test JuliaLowering.include_string(test_mod, "@ccall gc_safe=true strlen(\"asdf\"::Cstring)::Csize_t") == 4
@test JuliaLowering.include_string(test_mod, """
begin
    buf = zeros(UInt8, 20)
    @ccall sprintf(buf::Ptr{UInt8}, "num:%d str:%s"::Cstring; 42::Cint, "hello"::Cstring)::Cint
    String(buf)
end
""") == "num:42 str:hello\0\0\0\0"

let (err, st) = try
        JuliaLowering.include_string(test_mod, "@ccall strlen(\"foo\"::Cstring)")
    catch e
        e, stacktrace(catch_backtrace())
    end
    @test err isa JuliaLowering.MacroExpansionError
    @test err.msg == "expected a return type annotation `::SomeType`"
    @test isnothing(err.err)
    # Check that `catch_backtrace` can capture the stacktrace of the macro function
    @test any(sf->sf.func===:ccall_macro_parse, st)
end

# Tests for interop between old and new-style macros

# Hygiene interop:
# call_oldstyle_macro -> oldstyle -> newstyle3
JuliaLowering.include_string(test_mod, raw"""
    macro call_oldstyle_macro(a)
        @legacy_quote_to_syntax quote
            x = "x in call_oldstyle_macro"
            @oldstyle $a x
        end
    end

    macro newstyle3(a, b, c)
        @legacy_quote_to_syntax quote
            x = "x in @newstyle3"
            ($a, $b, $c, x)
        end
    end
""")
# TODO: Make this macro lowering go via JuliaSyntax rather than the flisp code
# (JuliaSyntax needs support for old-style quasiquote processing)
Base.eval(test_mod, :(
macro oldstyle(a, b)
    quote
        x = "x in @oldstyle"
        @newstyle3 $(esc(a)) $(esc(b)) x
    end
end
))
@test JuliaLowering.include_string(test_mod, """
let x = "x in outer scope"
    @call_oldstyle_macro x
end
""") == ("x in call_oldstyle_macro",
         "x in call_oldstyle_macro",
         "x in @oldstyle",
         "x in @newstyle3")
# #  would be ideal, but we can't get hygiene through oldstyle
# ("x in outer scope",
#  "x in call_oldstyle_macro",
#  "x in @oldstyle",
#  "x in @newstyle3")

# Old style unhygienic escaping with esc()
Base.eval(test_mod, :(
macro oldstyle_unhygienic()
    esc(:x)
end
))
@test JuliaLowering.include_string(test_mod, """
let x = "x in outer scope"
    @oldstyle_unhygienic
end
""") == "x in outer scope"

# Exceptions in old style macros
Base.eval(test_mod, :(
macro oldstyle_error()
    error("Some error in old style macro")
end
))
@test try
    JuliaLowering.include_string(test_mod, """
    @oldstyle_error
    """)
catch exc
    sprint(showerror, exc)
end == """
MacroExpansionError while expanding @oldstyle_error in module Main.macro_test:
@oldstyle_error
└─────────────┘ ── Error expanding macro
Caused by:
Some error in old style macro"""

# Old-style macros returning non-Expr values
Base.eval(test_mod, :(
macro oldstyle_non_Expr()
    42
end
))
@test JuliaLowering.include_string(test_mod, """
@oldstyle_non_Expr
""") === 42

# New-style macros called with the wrong arguments
JuliaLowering.include_string(test_mod, raw"""
macro method_error_test(a)
end
""")
Base.eval(test_mod, :(
macro method_error_test()
end
))
try
    JuliaLowering.include_string(test_mod, raw"""
    @method_error_test x y
    """)
    @test false
catch exc
    @test exc isa JuliaLowering.MacroExpansionError
    mexc = exc.err
    @test mexc isa MethodError
    @test mexc.args isa Tuple{JuliaLowering.MacroContext, JuliaLowering.SyntaxTree, JuliaLowering.SyntaxTree}
end

@testset "calling with old/new macro signatures" begin
    # Old defined with 1 arg, new with 2 args, both with 3 (but with different values)
    Base.eval(test_mod, :(macro sig_mismatch(x); x; end))
    Base.eval(test_mod, :(macro sig_mismatch(x, y, z); z; end))
    JuliaLowering.include_string(test_mod, "macro sig_mismatch(x, y); x; end")
    JuliaLowering.include_string(test_mod, "macro sig_mismatch(x, y, z); x; end")

    @test JuliaLowering.include_string(test_mod, "@sig_mismatch(1)") === 1
    @test JuliaLowering.include_string(test_mod, "@sig_mismatch(1, 2)") === 1
    @test JuliaLowering.include_string(test_mod, "@sig_mismatch(1, 2, 3)") === 1 # 3 if we prioritize old sig
    err = try
        JuliaLowering.include_string(test_mod, "@sig_mismatch(1, 2, 3, 4)") === 1
    catch exc
        sprint(showerror, exc, context=:module=>test_mod)
    end
    @test startswith(err, """
    MacroExpansionError while expanding @sig_mismatch in module Main.macro_test:
    @sig_mismatch(1, 2, 3, 4)
    └───────────────────────┘ ── Error expanding macro
    Caused by:
    MethodError: no method matching var"@sig_mismatch"(""")
end

@testset "old macros producing exotic expr heads (or are otherwise complex)" for expr_compat_mode in [true, false]
    @test JuliaLowering.include_string(test_mod, """
    let # example from @preserve docstring
        x = Ref{Int}(101)
        p = Base.unsafe_convert(Ptr{Int}, x)
        GC.@preserve x unsafe_load(p)
    end"""; expr_compat_mode) === 101 # Expr(:gc_preserve)

    # JuliaLowering.jl/issues/121
    @test JuliaLowering.include_string(test_mod, """
    GC.@preserve @static if true @__MODULE__ else end
    """) isa Module
    @test JuliaLowering.include_string(test_mod, """
    GC.@preserve @static if true v"1.14" else end
    """; expr_compat_mode) isa VersionNumber

    # JuliaLowering.jl/issues/144
    @test JuliaLowering.include_string(test_mod, """
    f_preserve144() = let
        val = Any[]
        GC.@preserve val begin; end
    end
    f_preserve144()
    """; expr_compat_mode) == nothing

    # JuliaLowering.jl/issues/145
    @test JuliaLowering.include_string(test_mod, """
    f_preserve145() = let
        debug_buffer = IOBuffer()
        # inside function to force compilation
        GC.@preserve debug_buffer 1
    end
    f_preserve145()
    """; expr_compat_mode) == 1

    # only invokelatest produces :isglobal now, so MWE here
    Base.eval(test_mod, :(macro isglobal(x); esc(Expr(:isglobal, x)); end))
    @test JuliaLowering.include_string(test_mod, """
    some_global = 1
    function isglobal_chk(some_arg)
       local some_local = 1
       (@isglobal(some_undefined), @isglobal(some_global), @isglobal(some_arg), @isglobal(some_local))
    end
    isglobal_chk(1)
    """; expr_compat_mode) === (true, true, false, false)
    # with K"Placeholder"s
    @test JuliaLowering.include_string(test_mod, """
    __ = 1
    function isglobal_chk(___)
       local ____ = 1
       (@isglobal(_), @isglobal(__), @isglobal(___), @isglobal(____))
    end
    isglobal_chk(1)
    """; expr_compat_mode) === (false, false, false, false)

    # @test appears to be the only macro in base to use :inert
    test_result = JuliaLowering.include_string(test_mod, """
    using Test
    @test identity(123) === 123
    """; expr_compat_mode)
    @test test_result.value === true

    # @enum produces Expr(:toplevel)
    JuliaLowering.include_string(test_mod, """
    @enum SOME_ENUM X1 X2 X3
    """; expr_compat_mode)
    Core.@latestworld
    @test test_mod.SOME_ENUM <: Enum
    @test test_mod.X1 isa Enum

    # @deprecate also produces Expr(:toplevel), and :public with expression
    # hygiene different from the contained names.
    @testset "@deprecate" begin
        @test JuliaLowering.include_string(test_mod, """
        module DeprecateMod
            d2(x) = x+1
            @deprecate d1(x) d2(0)
        end
        """; expr_compat_mode) isa Module
        Core.@latestworld
        @test isdefined(test_mod.DeprecateMod, :d2)
        @test isdefined(test_mod.DeprecateMod, :d1)
        @test Base.isexported(test_mod.DeprecateMod, :d1)
        @test !Base.isexported(test_mod, :d1)
    end

    # @testset produces :tryfinally with secret third arg
    @eval test_mod :(using Test)
    @test JuliaLowering.include_string(test_mod, "@test true") isa Test.Pass
    @testset let jltestset = JuliaLowering.include_string(test_mod, """
    @testset begin
        @test true
    end
    """; expr_compat_mode)
        @test jltestset isa Test.AbstractTestSet
        @test jltestset.n_passed == 1
    end

    # aliasscope
    @test jl_eval(
        test_mod,
        :(function simple_aliasscope(A, B)
              Base.Experimental.@aliasscope @inbounds for I in eachindex(A, B)
                  A[I] = Base.Experimental.Const(B)[I]
              end
              return 0
          end); expr_compat_mode) isa Function
    @test jl_eval(
        test_mod,
        :(let A = [1,2,3], B = [4,5,6]
              simple_aliasscope(A,B), A, B
          end); expr_compat_mode) == (0, [4,5,6], [4,5,6])
end

@testset "empty meta" begin
    @test fl_eval(test_mod, Expr(:meta)) == nothing
    @test fl_eval(test_mod, Expr(:block, Expr(:meta))) == nothing
    @test fl_eval(test_mod, Expr(:call,
                                 Expr(:function, Expr(:call, :func_empty_meta),
                                      Expr(:block, Expr(:meta))))) == nothing
    @test jl_eval(test_mod, Expr(:meta)) == nothing
    @test jl_eval(test_mod, Expr(:block, Expr(:meta))) == nothing
    @test jl_eval(test_mod, Expr(:call,
                                 Expr(:function, Expr(:call, :func_empty_meta),
                                      Expr(:block, Expr(:meta))))) == nothing
end

@testset "macros producing meta forms" for expr_compat_mode in [true, false]
    function find_method_ci(thunk)
        ci = thunk.args[1]::Core.CodeInfo
        m = findfirst(x->(x isa Expr && x.head === :method && length(x.args) === 3), ci.code)
        ci.code[m].args[3]
    end
    jlower_e(s) = JuliaLowering.to_lowered_expr(
        JuliaLowering.lower(
            test_mod, JuliaLowering.parsestmt(
                JuliaLowering.SyntaxTree, s);
            expr_compat_mode))

    prog = "Base.@assume_effects :foldable function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).purity === find_method_ci(our).purity

    prog = "Base.@inline function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).inlining === find_method_ci(our).inlining

    prog = "Base.@noinline function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).inlining === find_method_ci(our).inlining

    prog = "Base.@constprop :none function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).constprop === find_method_ci(our).constprop

    prog = "Base.@nospecializeinfer function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).nospecializeinfer === find_method_ci(our).nospecializeinfer

    prog = "Base.@propagate_inbounds function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).propagate_inbounds === find_method_ci(our).propagate_inbounds

    prog = "Base.@assume_effects :total @inline function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).inlining === find_method_ci(our).inlining
    @test find_method_ci(ref).purity === find_method_ci(our).purity

    prog = "Base.@assume_effects :consistent Base.@assume_effects :nothrow function foo(); end"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).purity === find_method_ci(our).purity

    prog = "Base.@pure @inline foo(x) = x + 1"
    ref = Meta.lower(test_mod, Meta.parse(prog))
    our = jlower_e(prog)
    @test find_method_ci(ref).purity === find_method_ci(our).purity
    @test find_method_ci(ref).inlining === find_method_ci(our).inlining

    # TODO: no api for option retrieval, just check that it compiles
    let options_mod = Module()
        @test fl_eval(options_mod, :(Base.Experimental.@optlevel 1)) == nothing
        @test jl_eval(options_mod, :(Base.Experimental.@optlevel 1)) == nothing
        @test fl_eval(options_mod, :(Base.Experimental.@max_methods 1)) == nothing
        @test jl_eval(options_mod, :(Base.Experimental.@max_methods 1)) == nothing
    end
end

# partially robot-generated
@testset "meta-like forms not using the `meta` expression" for expr_compat_mode in (true,false)
    @testset "in value position" begin
        @test fl_eval(test_mod, Expr(:boundscheck)) isa Bool
        @test jl_eval(test_mod, Expr(:boundscheck); expr_compat_mode) isa Bool

        @test fl_eval(test_mod, Expr(:inbounds, true)) === nothing
        @test fl_eval(test_mod, Expr(:inbounds, false)) === nothing
        @test fl_eval(test_mod, Expr(:inbounds, :pop)) === nothing
        @test jl_eval(test_mod, Expr(:inbounds, true); expr_compat_mode) === nothing
        @test jl_eval(test_mod, Expr(:inbounds, false); expr_compat_mode) === nothing
        @test jl_eval(test_mod, Expr(:inbounds, :pop); expr_compat_mode) === nothing

        @testset for inline in (:inline, :noinline)
            @testset let ex = Expr(:block,
                                   Expr(inline, true),
                                   Expr(inline, false))
                @test fl_eval(test_mod, ex) === nothing
                @test jl_eval(test_mod, ex; expr_compat_mode) === nothing
            end
            @testset let ex = Expr(:function, Expr(:tuple),
                                   Expr(:block,
                                        Expr(inline, true),
                                        Expr(inline, false)))
                local f
                f = fl_eval(test_mod, ex)
                Core.@latestworld
                @test f() === nothing

                f = jl_eval(test_mod, ex; expr_compat_mode)
                Core.@latestworld
                @test f() === nothing
            end
        end
    end

    function find_method_ci(thunk)
        ci = thunk.args[1]::Core.CodeInfo
        m = findfirst(x->(x isa Expr && x.head === :method && length(x.args) === 3), ci.code)
        ci.code[m].args[3]
    end
    jlower_e(s) = JuliaLowering.to_lowered_expr(
        JuliaLowering.lower(
            test_mod, JuliaLowering.parsestmt(
                JuliaLowering.SyntaxTree, s);
            expr_compat_mode))
    our_ssaflags(prog) = find_method_ci(jlower_e(prog)).ssaflags

    local INBOUNDS = Core.Compiler.IR_FLAG_INBOUNDS
    local INLINE   = Core.Compiler.IR_FLAG_INLINE
    local NOINLINE = Core.Compiler.IR_FLAG_NOINLINE

    # `compute_ssaflags` shifts the encoded purity overrides up by NUM_IR_FLAGS.
    purity_mask(eo::Base.EffectsOverride) =
        UInt32(Base.encode_effects_override(eo)) << Core.Compiler.NUM_IR_FLAGS

    # check any IR statement in `prog` has `flags`
    has_any(prog, flags) = any(f -> (f & flags) == flags, our_ssaflags(prog))
    has_none(prog, flags) = all(f -> (f & flags) == 0,    our_ssaflags(prog))

    @testset "boundscheck" begin
        JuliaLowering.include_string(test_mod, """
        @inline function g_boundscheck(A, i)
            @boundscheck checkbounds(A, i)
            return A[i]
        end
        """; expr_compat_mode)
        @test test_mod.g_boundscheck(1:2, 2) == 2
        @test_throws BoundsError test_mod.g_boundscheck(1:2, 3)

        # The boundscheck marker itself does not set IR_FLAG_INBOUNDS — it is
        # a separate runtime predicate, not an annotation.
        @test has_none("function f(A,i); @boundscheck checkbounds(A,i); A[i]; end",
                       INBOUNDS)
        # `Expr(:boundscheck)` should survive lowering as a top-level
        # statement (it gets rewritten by inlining/codegen, not lowering).
        let our = find_method_ci(jlower_e(
                "function f(A,i); @boundscheck checkbounds(A,i); A[i]; end"))
            @test any(s -> s isa Expr && s.head === :boundscheck, our.code)
        end
    end

    @testset "inbounds" begin
        JuliaLowering.include_string(test_mod, """
        function sum_inbounds(A::AbstractArray)
            r = zero(eltype(A))
            for i in eachindex(A)
                @inbounds r += A[i]
            end
            return r
        end
        """; expr_compat_mode)
        @test test_mod.sum_inbounds([1,2,3]) == 6

        @test has_none("function f(A,i); A[i]; end", INBOUNDS)
        @test has_any("function f(A,i); @inbounds A[i]; end", INBOUNDS)
        @test has_any("""
            function f(A)
                s = zero(eltype(A))
                @inbounds for i in eachindex(A)
                    s += A[i]
                end
                s
            end
        """, INBOUNDS)
        let flags = our_ssaflags("""
                function f(A, i, j)
                    z = @inbounds A[i]
                    A[j]
                end
            """)
            @test any(f -> (f & INBOUNDS) != 0, flags)  # inside @inbounds
            @test any(f -> (f & INBOUNDS) == 0, flags)  # outside
        end
    end

    @testset "inline" begin
        @test has_any("function f(g,x); @inline g(x); end", INLINE)
        @test has_none("function f(g,x); g(x); end", INLINE)
        @test has_none("function f(g,x); @inline g(x); end", NOINLINE)
        @test has_any("function f(g,x); @inline g(x) + g(x); end", INLINE)

        # Bare `@inline` inside a function body (1.8+) emits
        # `Expr(:meta, :inline)`; no statement gets a call-site IR_FLAG_INLINE.
        JuliaLowering.include_string(test_mod, """
        function bare_inline(x)
            @inline
            x * 2
        end
        """; expr_compat_mode)
        @test test_mod.bare_inline(3) == 6
        @test has_none("function f(x); @inline; x * 2; end", INLINE)

        # `@inline` on a definition is handled by the meta-expression path
        # (covered in "macros producing meta forms"); confirm it still runs
        # and that no call-site INLINE bit leaks into the body.
        JuliaLowering.include_string(test_mod, """
        @inline f_inline_def(x) = x + 1
        """; expr_compat_mode)
        @test test_mod.f_inline_def(2) == 3
        @test has_none("@inline f(x) = x + 1", INLINE)
    end

    @testset "noinline" begin
        # Analogous to `@inline` but pushes IR_FLAG_NOINLINE.
        @test has_any("function f(g,x); @noinline g(x); end", NOINLINE)
        @test has_none("function f(g,x); g(x); end", NOINLINE)
        @test has_none("function f(g,x); @noinline g(x); end", INLINE)
        @test has_any("function f(g,x); @noinline g(x) + g(x); end", NOINLINE)

        JuliaLowering.include_string(test_mod, """
        function bare_noinline(x)
            @noinline
            x * 2
        end
        """; expr_compat_mode)
        @test test_mod.bare_noinline(3) == 6
        @test has_none("function f(x); @noinline; x * 2; end", NOINLINE)

        JuliaLowering.include_string(test_mod, """
        @noinline f_noinline_def(x) = x + 1
        """; expr_compat_mode)
        @test test_mod.f_noinline_def(2) == 3

        # Innermost annotation wins when @inline / @noinline nest: the inner
        # call gets IR_FLAG_INLINE; the outer @noinline still applies to
        # statements outside the inner region.
        let flags = our_ssaflags("""
                function f(g, x)
                    @noinline let
                        a = @inline g(x)
                        b = g(x)
                        (a, b)
                    end
                end
            """)
            @test any(f -> (f & INLINE)   != 0, flags)
            @test any(f -> (f & NOINLINE) != 0, flags)
        end
    end

    @testset "purity" begin
        # Sanity: plain function with no purity annotation has no purity bits set.
        @test has_none("function f(g,x); g(x); end",
                       UInt32(0xFFFF) << Core.Compiler.NUM_IR_FLAGS)
        # `@assume_effects :foo expr` at a call site expands to
        #   (block (purity ...11 bool args...) (local (= val expr)) (purity) val)
        # where the trailing zero-arg `(purity)` is the region-end token.
        @test has_any("function f(g,x); Base.@assume_effects :nothrow g(x); end",
                      purity_mask(Base.EffectsOverride(nothrow=true)))
        # Multiple atomic settings combine to set both bits at once.
        @test has_any(
            "function f(g,x); Base.@assume_effects :consistent :effect_free g(x); end",
            purity_mask(Base.EffectsOverride(consistent=true, effect_free=true)))

        # Function form goes through a different path: `(meta (purity args...))`
        JuliaLowering.include_string(test_mod, """
        Base.@assume_effects :total f_assume_def(x) = x
        """; expr_compat_mode)
        @test test_mod.f_assume_def(5) == 5
        prog_def = "Base.@assume_effects :total function f_assume_total(x); x; end"
        ref_ci = find_method_ci(Meta.lower(test_mod, Meta.parse(prog_def)))
        our_ci = find_method_ci(jlower_e(prog_def))
        @test ref_ci.purity === our_ci.purity
    end
end

@testset "scope layers for normally-inert ASTs" begin
    # Right hand side of `.`
    @test JuliaLowering.include_string(test_mod, raw"""
    let x = @legacy_quote_to_syntax :(hi)
        @legacy_quote_to_syntax :(A.$x)
    end
    """) ≈ @ast_ [K"."
        "A"::K"Identifier"
        [K"inert" "hi"::K"Identifier"]
    ]
    # module
    @test JuliaLowering.include_string(test_mod, raw"""
    let x = @legacy_quote_to_syntax :(AA)
        @legacy_quote_to_syntax :(module $x end)
    end
    """) ≈ @ast_ [K"module"
        v"1.14.0"::K"Value"
        true::K"Value"
        "AA"::K"Identifier"
        [K"block"]
    ]

    # In macro expansion, require that expressions passed in as macro
    # *arguments* get the lexical scope of the calling context, even for the
    # `x` in `M.$x` where the right hand side of `.` is normally quoted.
    @test JuliaLowering.include_string(test_mod, raw"""
        let x = @legacy_quote_to_syntax :(someglobal)
            @eval M.$x
        end
    """; expr_compat_mode=false) == "global in module M"
    @test JuliaLowering.include_string(test_mod, raw"""
        let x = @legacy_quote_to_syntax :(someglobal)
            @eval M.$x
        end
    """; expr_compat_mode=true) == "global in module M"

    # @eval quoting should embed the value, not the syntax
    @test JuliaLowering.include_string(test_mod, raw"""
        let some_local = 101
            @eval module AA
                x = $some_local
            end
        end
    """; expr_compat_mode=false) isa Module
    @test test_mod.AA.x == 101
    @test JuliaLowering.include_string(test_mod, raw"""
        let some_local = 101
            @eval module AA
                x = $some_local
            end
        end
    """; expr_compat_mode=true) isa Module
    @test test_mod.AA.x == 101

    # "Deferred hygiene" in macros which emit quoted code.  OK to break
    #
    # The old macro system doesn't handle this - here's the equivalent
    # implementation
    # macro make_quoted_code(init, y)
    #     QuoteNode(:(let
    #         x = "inner x"
    #         $(esc(init))
    #         ($(esc(y)), x)
    #     end))
    # end
    JuliaLowering.include_string(test_mod, raw"""
    macro make_quoted_code(init, y)
        q = @legacy_quote_to_syntax :(let
            x = "inner x"
            $init
            ($y, x)
        end)
        @ast q._graph q [K"syntaxinert" q]
    end
    """)
    code = JuliaLowering.include_string(test_mod, """@make_quoted_code(x="outer x", x)""")
    @test JuliaLowering.eval(test_mod, code) == ("outer x", "inner x")
end

@testset "toplevel macro hygiene" for run in [JuliaLowering.include_string,
                                              Base.include_string]
    @eval test_mod global mod = $test_mod
    @eval test_mod module MacroMod
    global mod = MacroMod
    macro escaped_toplevel()
        esc(Expr(:toplevel, :(mod)))
    end
    macro inner_escaped_toplevel()
        Expr(:toplevel, esc(:(mod)))
    end
    macro unescaped_toplevel()
        Expr(:toplevel, :(mod))
    end
    end
    Core.@latestworld
    @test run(test_mod, "MacroMod.@escaped_toplevel") === test_mod
    @test run(test_mod, "MacroMod.@inner_escaped_toplevel") === test_mod
    @test run(test_mod, "MacroMod.@unescaped_toplevel") === test_mod.MacroMod

    unrelated = @newmod(unrelated)
    @eval unrelated const MacroMod = $(test_mod.MacroMod)
    @eval unrelated global mod = 123

    @test run(unrelated, "MacroMod.@escaped_toplevel") == 123
    @test run(unrelated, "MacroMod.@inner_escaped_toplevel") == 123
    @test run(unrelated, "MacroMod.@unescaped_toplevel") === test_mod.MacroMod
end

@testset "toplevel macro hygiene: @__MODULE__" for run in [JuliaLowering.include_string,
                                                           Base.include_string]
    @eval test_mod module MacroMod
    macro atmodule_in_toplevel()
        Expr(:toplevel, :(@__MODULE__))
    end
    macro atmodule_in_module()
        Expr(:toplevel, Expr(:module, true, esc(:atmod_mod), Expr(
            :block, :(global global_mod = @__MODULE__))))
    end
    end
    Core.@latestworld
    @test run(test_mod, "MacroMod.@atmodule_in_toplevel") === test_mod
    @test run(test_mod, "MacroMod.@atmodule_in_module") isa Module
    Core.@latestworld
    @test isdefined(test_mod, :atmod_mod)
    @test test_mod.atmod_mod.global_mod == test_mod.atmod_mod
end

# JuliaLang/JuliaLowering.jl#120
#
# `__module__` should be expanded as the lexical module containing the expanded
# code, not the module corresponding to the current hygienic scope
JuliaLowering.include_string(test_mod, raw"""
module Mod1
import ..JuliaLowering.@legacy_quote_to_syntax
macro indirect_MODULE()
    return @legacy_quote_to_syntax :(@__MODULE__())
end
end
""")
code = JuliaLowering.include_string(test_mod, """Mod1.@indirect_MODULE()""")
@test JuliaLowering.eval(test_mod, code) === test_mod # !== test_mod.Mod1
# the lowering/eval iterator needs to expand in the correct world age (currently
# the only way to hit this from user code is macros producing toplevel)

@testset "old macros defining modules" begin
    # escaped module nested in tmpmod_1
    jl_eval(test_mod, :(
        module MacMod
        macro makemod(name)
            Expr(:toplevel,
                 esc(Expr(:module, false, :tmpmod_1,
                          Expr(:block,
                               Expr(:module, false, name,
                                    Expr(:block, Expr(:const, Expr(:(=), :c, 1))))))))
        end
        end); expr_compat_mode=true)

    @testset for expr_compat_mode in [true, false]
        @test JuliaLowering.include_string(
            test_mod, "MacMod.@makemod(newmod)") isa Module
        Core.@latestworld
        # module name should escape macmod->test_mod
        @test test_mod.tmpmod_1.newmod isa Module
        @test !isdefined(test_mod.MacMod, :newmod)
        @test !isdefined(test_mod.MacMod, :tmpmod_1)
        # const in mod body should work
        @test test_mod.tmpmod_1.newmod.c == 1
    end

    # escaped module name
    jl_eval(test_mod, :(
        module MacMod
        macro makemod(name)
            Expr(:toplevel,
                 Expr(:module, false, esc(name),
                      Expr(:block,
                           # TODO: escape node in outer context
                           # Expr(:const, Expr(:(=), esc(:c), 1))
                           )))
        end
        end); expr_compat_mode=true)

    @testset for expr_compat_mode in [true, false]
        @test JuliaLowering.include_string(
            test_mod, "MacMod.@makemod(newmod)") isa Module
        Core.@latestworld
        # module name should escape macmod->test_mod
        @test test_mod.newmod isa Module
        @test !isdefined(test_mod.MacMod, :newmod)
        # const in mod body should
        @test_broken test_mod.newmod.c == 1
    end
end

@testset "(AI) old macro attribution survives a nested eval in its body (#32)" begin
    Base.eval(test_mod, :(module MacDefMod
        const secret = 99
        macro getsecret()
            __module__.eval(:(nested_eval_side_effect = 1 + 1))
            return :(secret)   # bare name -> resolves in the defining module
        end
    end))
    Core.@latestworld
    # `secret` must resolve in MacDefMod (== mod_for_ast), matching flisp.
    @test JuliaLowering.include_string(test_mod, "MacDefMod.@getsecret()") == 99
    @test test_mod.nested_eval_side_effect == 2
    @test fl_eval(test_mod, :(MacDefMod.@getsecret())) == 99
end

@testset "macros defining macros" begin
    @eval test_mod macro make_and_use_macro_toplevel()
        Expr(:toplevel,
             esc(:(macro from_toplevel_expansion()
                   :(123)
               end)),
             esc(:(@from_toplevel_expansion())))
    end

    @test JuliaLowering.include_string(
        test_mod, "@make_and_use_macro_toplevel()"; expr_compat_mode=true) === 123

    if isdefined(test_mod, Symbol("@from_toplevel_expansion"))
        Base.delete_binding(test_mod, Symbol("@from_toplevel_expansion"))
    end

    @test JuliaLowering.include_string(
        test_mod, "@make_and_use_macro_toplevel()"; expr_compat_mode=false) === 123
end

@testset "SIMD loopinfo" begin
    @test JuliaLowering.include_string(test_mod, raw"""
    @eval let
        n = 10
        x = zeros(n)
        i = 1
        while i ≤ n
            x[i] += 1
            i += 1
            $(Expr(:loopinfo, Symbol("julia.simdloop"), nothing))  # Mark loop as SIMD loop
        end
        sum(x)
    end
    """; expr_compat_mode=true) == 10.0

    @test JuliaLowering.include_string(test_mod, raw"""
    @eval let
        n = 10
        x = zeros(n)
        i = 1
        while i ≤ n
            x[i] += 1
            i += 1
            $(Expr(:loopinfo, Symbol("julia.simdloop"), Symbol("julia.ivdep")))  # Mark loop as SIMD loop
        end
        sum(x)
    end
    """; expr_compat_mode=true) == 10.0

    JuliaLowering.include_string(test_mod, """
    @noinline function inner(x, y)
        s = zero(eltype(x))
        for i in eachindex(x, y)
            @inbounds s += x[i]*y[i]
        end
        return s
    end
    """)

    JuliaLowering.include_string(test_mod, """
    @noinline function innersimd(x, y)
        s = zero(eltype(x))
        @simd for i in eachindex(x, y)
            @inbounds s += x[i] * y[i]
        end
        return s
    end
    """)

    @test test_mod.inner([1,2,3], [1,2,3]) == 14
    @test test_mod.innersimd([1,2,3], [1,2,3]) == 14
end

@testset "@__FUNCTION__ and Expr(:thisfunction)" begin
    @testset "Basic usage" begin
        # @__FUNCTION__ in regular functions
        JuliaLowering.include_string(test_mod, raw"""
        test_function_basic() = @__FUNCTION__
        """; expr_compat_mode=true)
        @test test_mod.test_function_basic() === test_mod.test_function_basic

        # Expr(:thisfunction) in regular functions
        JuliaLowering.include_string(test_mod, raw"""
            @eval regular_func() = @__FUNCTION__
        """; expr_compat_mode=true)
        @test test_mod.regular_func() === test_mod.regular_func
    end

    @testset "Recursion" begin
        # Factorial with @__FUNCTION__
        JuliaLowering.include_string(test_mod, raw"""
        factorial_function(n) = n <= 1 ? 1 : n * (@__FUNCTION__)(n - 1)
        """; expr_compat_mode=true)
        @test test_mod.factorial_function(5) == 120

        # Fibonacci with Expr(:thisfunction)
        JuliaLowering.include_string(test_mod, raw"""
        struct RecursiveCallableStruct; end
        (::RecursiveCallableStruct)(n) = n <= 1 ? n : @__FUNCTION__()(n-1) + @__FUNCTION__()(n-2)
        """; expr_compat_mode=true)
        @test test_mod.RecursiveCallableStruct()(10) === 55

        # Anonymous function recursion
        @test JuliaLowering.include_string(test_mod, raw"""
        (n -> n <= 1 ? 1 : n * (@__FUNCTION__)(n - 1))(5)
        """; expr_compat_mode=true) == 120
    end

    @testset "Closures and nested functions" begin
        # Prevents boxed closures
        JuliaLowering.include_string(test_mod, raw"""
        function make_closure()
            fib(n) = n <= 1 ? 1 : (@__FUNCTION__)(n - 1) + (@__FUNCTION__)(n - 2)
            return fib
        end
        """; expr_compat_mode=true)
        Test.@inferred test_mod.make_closure()
        closure = test_mod.make_closure()
        @test closure(5) == 8
        Test.@inferred closure(5)

        # Complex closure of closures
        JuliaLowering.include_string(test_mod, raw"""
        function f1()
            function f2()
                function f3()
                    return @__FUNCTION__
                end
                return (@__FUNCTION__), f3()
            end
            return (@__FUNCTION__), f2()...
        end
        """; expr_compat_mode=true)
        Test.@inferred test_mod.f1()
        @test test_mod.f1()[1] === test_mod.f1
        @test test_mod.f1()[2] !== test_mod.f1
        @test test_mod.f1()[3] !== test_mod.f1
        @test test_mod.f1()[3]() === test_mod.f1()[3]
        @test test_mod.f1()[2]()[2]() === test_mod.f1()[3]
    end

    @testset "Do blocks" begin
        function test_do_block()
            result = JuliaLowering.include_string(test_mod, raw"""
            map([1, 2, 3]) do x
                return (@__FUNCTION__, x)
            end
            """; expr_compat_mode=true)
            # All should refer to the same do-block function
            @test all(r -> r[1] === result[1][1], result)
            # Values should be different
            @test [r[2] for r in result] == [1, 2, 3]
            # It should be different than `test_do_block`
            @test result[1][1] !== test_do_block
        end
        test_do_block()
    end

    @testset "Keyword arguments" begin
        # @__FUNCTION__ with kwargs
        JuliaLowering.include_string(test_mod, raw"""
        f_thisfunction_kw(; n) = n <= 1 ? 1 : n * (@__FUNCTION__)(; n = n - 1)
        """; expr_compat_mode=true)
        @test test_mod.f_thisfunction_kw(n = 5) == 120

        # Expr(:thisfunction) with kwargs
        JuliaLowering.include_string(test_mod, raw"""
        f_thisfunction_kw2(; n=1) = n <= 1 ? n : n * @__FUNCTION__()(; n=n-1)
        """; expr_compat_mode=true)
        result = test_mod.f_thisfunction_kw2(n=5)
        @test result == 120
    end

    @testset "Callable structs" begin
        # @__FUNCTION__ in callable structs
        JuliaLowering.include_string(test_mod, raw"""
        module A
            struct CallableStruct{T}; val::T; end
            (c::CallableStruct)() = @__FUNCTION__
        end
        """; expr_compat_mode=true)
        JuliaLowering.include_string(test_mod, raw"""
        using .A: CallableStruct
        """; expr_compat_mode=true)
        c = test_mod.CallableStruct(5)
        @test c() === c

        # In closures, var"#self#" should refer to the enclosing function,
        # NOT the enclosing struct instance
        JuliaLowering.include_string(test_mod, raw"""
        struct CallableStruct2; end
        @eval function (obj::CallableStruct2)()
            function inner_func()
                @__FUNCTION__
            end
            inner_func
        end
        """; expr_compat_mode=true)

        let cs = test_mod.CallableStruct2()
            @test cs()() === cs()
            @test cs()() !== cs
        end

        # Accessing values via self-reference
        JuliaLowering.include_string(test_mod, raw"""
        struct CallableStruct3
            value::Int
        end
        (obj::CallableStruct3)() = @__FUNCTION__()
        (obj::CallableStruct3)(x) = @__FUNCTION__().value + x
        """; expr_compat_mode=true)

        let cs = test_mod.CallableStruct3(42)
            @test cs() === cs
            @test cs(10) === 52
        end

        # Callable struct with args and kwargs
        JuliaLowering.include_string(test_mod, raw"""
        struct CallableStruct4
        end
        @eval function (obj::CallableStruct4)(x, args...; y=2, kws...)
            return (; func=(@__FUNCTION__), x, args, y, kws)
        end
        """; expr_compat_mode=true)
        c = test_mod.CallableStruct4()
        @test c(1).func === c
        @test c(2, 3).args == (3,)
        @test c(2; y=4).y == 4
        @test c(2; y=4, a=5, b=6, c=7).kws[:c] == 7
    end

    @testset "Special cases" begin
        # Generated functions
        JuliaLowering.include_string(test_mod, raw"""
        let
            @generated foo2() = @__FUNCTION__
            foo2() === foo2
        end
        """; expr_compat_mode=true)

        # Struct constructors
        let
            JuliaLowering.include_string(test_mod, raw"""
            struct Cols{T<:Tuple}
                cols::T
                operator
                Cols(args...; operator=union) = (new{typeof(args)}(args, operator); string(@__FUNCTION__))
            end
            """; expr_compat_mode=true)
            result = @invokelatest test_mod.Cols(1, 2, 3)
            @test occursin("Cols", result)
        end

        # Should not access arg-map for local variables
        # TODO: worth the special case?
        JuliaLowering.include_string(test_mod, raw"""
            function f_thisfunction_argmap end
            function (f_thisfunction_argmap::typeof(f_thisfunction_argmap))()
                f_thisfunction_argmap = 1
                @__FUNCTION__
            end
        """; expr_compat_mode=true)
        @test_broken test_mod.f_thisfunction_argmap() ===
            test_mod.f_thisfunction_argmap
    end

    @test JuliaLowering.include_string(test_mod, """
        @eval let f=[ ()->$(Expr(:thisfunction)) for i = 1:1 ][1]; f() === f; end
    """; expr_compat_mode=true)
end

@testset "macro source LineNumberNode" begin
    Base.include_string(test_mod, raw"""
    macro srcfile()
        string(__source__.file)
    end
    """)

    mac_ex = Expr(:macrocall, Symbol("@srcfile"), LineNumberNode(1, "goodfile"))
    mac_st = JuliaLowering.expr_to_est(mac_ex, LineNumberNode(1, "badfile"))

    @test JuliaLowering.eval(test_mod, mac_st) === "goodfile"

    # tolerate nothing
    mac_ex = Expr(:macrocall, Symbol("@srcfile"), nothing)
    mac_st = JuliaLowering.expr_to_est(mac_ex, LineNumberNode(1, "badfile"))
    @test JuliaLowering.eval(test_mod, mac_st) == "none"
end

@testset "macro QuoteNode + inert behavior" begin
    Base.include_string(test_mod, raw"""
    macro quoted_gr()
        QuoteNode(GlobalRef(Base, :dontresolveme))
    end
    """)
    let gr = JuliaLowering.include_string(test_mod, "@quoted_gr")
        @test gr.mod === Base
        @test gr.name === :dontresolveme
    end
end

@testset "Base macros" begin
    jl_eval(test_mod,
            :(function test_invokelatest()
                  @eval invokelatest_target(x, y) = x + y
                  out = @invokelatest(invokelatest_target(1, 2))
                  Base.delete_binding(@__MODULE__, :invokelatest_target)
                  out
              end))
    # the following test needs to define this to be effective
    @test_throws UndefVarError JuliaLowering.include_string(test_mod, "invokelatest_target(1,2)")
    @test JuliaLowering.include_string(test_mod, "test_invokelatest()") === 3

    for expr_compat_mode in (false, true),
        version in (v"1.13", v"1.14")

        _version = JuliaLowering.include_string(test_mod,
            "Base.Experimental.@VERSION";
            expr_compat_mode, version
        )
        @test _version isa NamedTuple
        @test _version.syntax == version
    end
end

# produces import/using in module that is `@eval`ed.
@testset "safetestset" begin
    macro_mod = @newmod(macro_mod, test_mod)
    JuliaLowering.include_string(macro_mod, raw"""
    macro safetestset(testname, expr)
        quote
            @eval module $(gensym("safetestset_mod"))
            using Test
            @testset $testname $expr
            end
            nothing
        end
    end
    """; expr_compat_mode=true)

    JuliaLowering.include_string(test_mod, """
    macro_mod.@safetestset "Tests" begin
        a = 1; b = 2; c = a + b; @test c == 3
        @isdefined(a) == true
    end
    """; expr_compat_mode=true)
    @test !isdefined(test_mod, :a)
    @test !isdefined(macro_mod, :a)
end

@testset "(AI) single-arg @eval targets the dynamic module (#17)" for expr_compat_mode in (true, false)
    # flisp passes `__module__` = the module the code is currently being
    # expanded/evaluated into (`jl_expand_macros`'s `inmodule`) to every macro,
    # at any nesting depth inside other macros' expansions; only macro *name*
    # resolution uses the hygiene context. Single-arg `@eval` (and `@__MODULE__`
    # in re-evaluated quoted payloads) must therefore act on the dynamic
    # evaluation module, not on `syntax_module(macrocall)` (the macro-defining
    # module for a macro-generated `@eval`). This is what SafeTestsets'
    # `@safetestset` relies on: `@eval module $mod; using Test; ... end` must
    # create the module under the *caller*, where Test is loadable.
    root = Module(gensym(:eval_dynmod))
    @eval root import JuliaLowering
    JuliaLowering.include_string(root, raw"""
    module MacB
        import JuliaLowering.@legacy_quote_to_syntax
        macro do_eval()
            @legacy_quote_to_syntax quote
                @eval (@__MODULE__)
            end
        end
    end
    module MacA
        import JuliaLowering.@legacy_quote_to_syntax
        import ..MacB
        macro wrap()
            @legacy_quote_to_syntax quote
                @eval (@__MODULE__)
            end
        end
        macro via_b()
            @legacy_quote_to_syntax quote
                MacB.@do_eval()
            end
        end
        macro wrap_ee()
            @legacy_quote_to_syntax quote
                @eval @eval (@__MODULE__)
            end
        end
        macro wrap_two_arg()
            # two-arg control: explicit target module; the payload's
            # `@__MODULE__` must still see the *target* module
            @legacy_quote_to_syntax quote
                @eval MacB (@__MODULE__)
            end
        end
        macro wrap_arg(ex)
            # caller-provided payload (caller's hygiene layer)
            @legacy_quote_to_syntax quote
                @eval $ex
            end
        end
        macro wrap_fn()
            # `@eval` captures the module current when the enclosing function
            # *definition* is expanded, like flisp
            @legacy_quote_to_syntax quote
                () -> @eval (@__MODULE__)
            end
        end
        macro mkmod()
            mod = gensym("EvalMod")
            @legacy_quote_to_syntax quote
                @eval module $mod
                    const inside = (@__MODULE__)
                end
            end
        end
        macro mkmod_payload(ex)
            mod = gensym("EvalMod2")
            @legacy_quote_to_syntax quote
                @eval module $mod
                    $ex
                end
            end
        end
    end
    module Sub
        import ..MacA
    end
    """; expr_compat_mode)
    Core.@latestworld

    run(str) = JuliaLowering.include_string(root, str; expr_compat_mode)

    # Lexical (non-macro-generated) cases: unchanged behavior
    @test run("@eval (@__MODULE__)") === root
    @test run("(() -> @eval (@__MODULE__))()") === root
    @test run("@eval @eval (@__MODULE__)") === root

    # `@eval` inside another macro's unescaped expansion evaluates in the
    # caller's module, not the macro's
    @test run("MacA.@wrap()") === root
    # ... even when the `@eval`-ing macro is called by another macro's expansion
    # (flisp: still the dynamic module, not either macro's module)
    @test run("MacA.@via_b()") === root
    # `@eval` nested in `@eval` re-expands against the outer target
    @test run("MacA.@wrap_ee()") === root
    # two-arg control: explicit module wins; payload `@__MODULE__` follows it
    @test run("MacA.@wrap_two_arg()") === root.MacB
    # macro-generated closure: `@eval` binds the definition-time module
    @test Base.invokelatest(run("MacA.@wrap_fn()")) === root
    # the same macro evaluated into a different module follows the live module
    @test JuliaLowering.include_string(
        root.Sub, "MacA.@wrap()"; expr_compat_mode) === root.Sub

    # Caller-provided payloads evaluate in the caller's module
    @test run("MacA.@wrap_arg(arg_marker = (@__MODULE__))") === root
    if !expr_compat_mode
        # With SyntaxTree-passed arguments the payload keeps the caller's
        # hygiene: the global lands in `root` and is visible there. (In
        # expr_compat_mode the old-style Expr round-trip re-layers the payload
        # with the macro's hygiene and the assignment becomes a hygienic
        # toplevel local -- a pre-existing divergence from flisp tracked by
        # the "hygienic toplevel assignments" TODO in scope_analysis.jl.)
        @test Base.invokelatest(isdefined, root, :arg_marker)
        @test Base.invokelatest(getfield, root, :arg_marker) === root
    end

    # The SafeTestsets shape: a macro-generated `@eval module $mod ... end`
    # creates the module under the dynamic (caller) module
    m = run("MacA.@mkmod()")
    @test m isa Module
    @test parentmodule(m) === root
    @test Base.invokelatest(getfield, m, :inside) === m
    # ... and user payload interpolated into the module body sees the fresh
    # module as its dynamic module (a user's own `@eval` inside a
    # `@safetestset` acts on the anonymous test module)
    m2 = run("MacA.@mkmod_payload(@eval user_marker = (@__MODULE__))")
    @test m2 isa Module
    @test parentmodule(m2) === root
    @test Base.invokelatest(getfield, m2, :user_marker) === m2

    if expr_compat_mode
        # Escaped expansions (old-style macros only): same dynamic target
        JuliaLowering.include_string(root, raw"""
        module MacEsc
            macro wrap_esc()
                esc(quote
                    @eval esc_marker = (@__MODULE__)
                end)
            end
        end
        """; expr_compat_mode)
        Core.@latestworld
        @test run("MacEsc.@wrap_esc()") === root
        @test Base.invokelatest(isdefined, root, :esc_marker)
        @test Base.invokelatest(getfield, root, :esc_marker) === root
    end

    # An old-style (flisp-defined and -lowered) macro whose expansion calls
    # `@eval` gets the same treatment when invoked under JuliaLowering
    fl_eval(root, :(module MacFl
        macro flwrap()
            quote
                @eval (@__MODULE__)
            end
        end
    end))
    Core.@latestworld
    @test run("MacFl.@flwrap()") === root
end

@testset "(AI) @generated function generator stub binds in eval target" begin
    # An old-style macro (home module `GenHome`) that expands to an unescaped
    # `@generated function $GenHome.thefun(...)` extends a *qualified* function,
    # but the `@generated` form's internal generator-stub global
    # (`#_@generator#N` and its closure type) is fresh, invisible machinery.
    # flisp mangles that stub as a gensym'd anonymous function of the module
    # the top-level form is evaluated into (the call site), never the macro's
    # home; a downstream package precompiling such a macro from a *closed*
    # dependency would otherwise fail with "Creating a new global in closed
    # module".  This is the Adapt `@adapt_structure` shape (ClimaComms,
    # DiffusionGarnet, SliceSampling); regression from dedc5dd37d, which bound
    # the stub via `syntax_module(src)` (the macro home) instead of the eval
    # target.
    m = Module()
    Core.eval(m, :(import JuliaLowering))
    JuliaLowering.include_string(m, raw"""
    module GenHome
        thefun(x) = error("fallback should never run")
        macro mkgen(T)
            quote
                @generated function $GenHome.thefun(x::$(esc(T)))
                    :(1)
                end
            end
        end
    end
    module GenCall
        using ..GenHome: @mkgen
        struct S end
        @mkgen S
    end
    """; expr_compat_mode=true)
    Core.@latestworld
    gen(mod) = filter(n -> occursin("generator", string(n)), names(mod; all=true))
    # The generator stub landed in the call site, not the macro's home.
    @test isempty(gen(m.GenHome))
    @test !isempty(gen(m.GenCall))
    # ... and the generated method still fires and reads the stub correctly.
    @test Base.invokelatest(m.GenHome.thefun, Base.invokelatest(m.GenCall.S)) == 1
end

@testset "(AI) @generated stub reserves at call site for interpolated GlobalRef" begin
    # Straggler guard for THRASH-ANALYSIS cluster 1 ("@eval/module-targeting
    # hygiene"): the @generated generator-stub reservation
    # (`generated_method_defs`, desugaring.jl) is the sibling of the kw-body
    # reservation, and the kw-body site regressed on exactly this shape three
    # days after the stub was first fixed (commit 2e5b6be275 vs 5768eaa790 /
    # aaccaa2c89).  When the extended function's name arrives as an interpolated
    # `GlobalRef` *value*, `compat.jl` stamps a `:mod` attribute on the name node
    # that short-circuits `syntax_module` straight to the owner module; a stub
    # reserved via that module would land in a possibly-closed dependency.  The
    # sibling kw-body path is pinned for this vector in test/functions.jl; pin it
    # here for the generator stub too.  Both machineries reserve in
    # `ctx.layer.mod` (the module being lowered into), so the stub must land in
    # the extending module, never in the owner.  Verified non-vacuous: reserving
    # via `syntax_module(mtable)` instead lands the stub in `OwnerG`.
    genstub(mod) = filter(n -> occursin("generator", string(n)), names(mod; all=true))

    OwnerG = Module()
    JuliaLowering.include_string(OwnerG, "gfun(x) = -1")
    o_before = Set(genstub(OwnerG))

    ExtG = Module()
    Core.eval(ExtG, :(import JuliaLowering))
    @eval ExtG const OwnerG = $OwnerG
    JuliaLowering.include_string(ExtG, raw"""
        let fn = GlobalRef(OwnerG, :gfun)
            @eval @generated function $fn(x::Int)
                :(x + 1000)
            end
        end
    """)
    Core.@latestworld

    # No new generator stub leaked into the owner (would be a closed module in the
    # incremental-precompile shape this models).
    @test isempty(setdiff(Set(genstub(OwnerG)), o_before))
    # ... it landed in the extending module.
    @test !isempty(genstub(ExtG))
    # ... and both the new @generated method and the original fallback dispatch.
    @test Base.invokelatest(OwnerG.gfun, 5) == 1005
    @test Base.invokelatest(OwnerG.gfun, 2.0) == -1
end

@testset "(AI) @eval payload-hygiene residual (known divergence)" begin
    # Bare `const` (and method-definition) payloads in macro-generated @eval
    # resolve their binding via the payload's hygiene module rather than the
    # (correctly threaded) eval-target module — a separate pre-existing
    # divergence from flisp, tracked as eval-payload-hygiene. The dynamic
    # module threading (#17) fixes the module/global payload shapes.
    m = Module()
    @test_broken try
        JuliaLowering.include_string(m, """
        module MacHome2
            macro make_const()
                :( @eval const CMARKER = 42 )
            end
        end
        MacHome2.@make_const()
        """)
        isdefined(m, :CMARKER)
    catch
        false   # currently throws/misbinds under JL; see bugs/eval-payload-hygiene
    end
end

# Old-style macros that build a function whose parameter *name* is escaped
# (`esc(:__ctx__)`) but whose body refers to that same symbol bare/unescaped.
# flisp binds the two by plain name (escaped argument names get an identity
# mapping in the expansion environment); JuliaLowering must match this for
# flisp-compatible expansions.  This is the ZygoteRules `@adjoint`/`gradm`
# pattern (`ZygoteRules.jl/src/adjoint.jl`).
fl_eval(test_mod, :(macro def_ctx_fn(fname)
    ctxparam = :($(esc(:__ctx__))::Any)
    quote
        function $(esc(fname))($ctxparam)
            return __ctx__ + 1     # bare ref must bind to the escaped parameter
        end
    end
end))
fl_eval(test_mod, :(macro def_ctx_closure(fname)
    ctxparam = :($(esc(:__ctx__))::Any)
    quote
        function $(esc(fname))($ctxparam)
            g() = __ctx__ + 1      # inner closure captures the escaped parameter
            return g()
        end
    end
end))
fl_eval(test_mod, :(macro def_ctx_multi(fname)
    a = :($(esc(:__a__))::Any)
    b = :($(esc(:__b__))::Any)
    quote
        function $(esc(fname))($a, $b)
            return __a__ + __b__
        end
    end
end))
# Hygiene must be preserved: a *nested* macro that emits a bare same-named
# reference belongs to a different expansion and must NOT bind to the outer
# escaped parameter (it stays an ordinary, here-undefined, global).
fl_eval(test_mod, :(macro hyg_inner(); quote __hyg__ + 100 end; end))
fl_eval(test_mod, :(macro def_ctx_hygiene(fname)
    hygparam = :($(esc(:__hyg__))::Any)
    quote
        function $(esc(fname))($hygparam)
            return @hyg_inner()    # must resolve to (undefined) global __hyg__
        end
    end
end))
# The alias is READ-only: flisp's identity mapping for escaped argument names
# is shadowed by the gensym-renaming of names *assigned* in the expansion, so
# an assigned bare name is a fresh hygienic local (here read-before-assigned),
# NOT the escaped parameter.
fl_eval(test_mod, :(macro def_ctx_assign(fname)
    ctxparam = :($(esc(:__ctx__))::Any)
    quote
        function $(esc(fname))($ctxparam)
            __ctx__ = __ctx__ + 5  # renamed: fresh local, used before assignment
            return __ctx__
        end
    end
end))
# Explicit `local` declarations must also be alias-blind: the bare name is
# declared as a fresh hygienic local (flisp gensym-renames it), not rejected
# as conflicting with the escaped parameter.
fl_eval(test_mod, :(macro def_ctx_local(fname)
    ctxparam = :($(esc(:__ctx__))::Any)
    quote
        function $(esc(fname))($ctxparam)
            local __ctx__ = 5      # fresh local, not the parameter
            return __ctx__
        end
    end
end))
# `global` declarations overlapping the escaped parameter: flisp reads the
# module global; under JuliaLowering this is the pre-existing (alias-blind,
# fix-independent) "globals may overlap args or sparams" divergence - see the
# `@test_broken` coverage in test/scopes.jl - because the relayered global
# collides with the escaped parameter's caller-layer binding.
fl_eval(test_mod, :(macro def_ctx_global(fname)
    ctxparam = :($(esc(:__ctx__))::Any)
    quote
        function $(esc(fname))($ctxparam)
            global __ctx__
            return __ctx__         # module global (999), not the parameter
        end
    end
end))
# A global of the same name exists in the macro-definition module: the escaped
# parameter must still win over it (flisp identity mapping shadows the global).
Base.eval(test_mod, :(global __ctx__ = 999))
Base.eval(test_mod, :(global __a__ = 999))
Base.eval(test_mod, :(global __b__ = 999))
Core.@latestworld

@testset "(AI) escaped parameter name, bare body reference (flisp compat)" for run in [
    (x::String)->fl_eval(test_mod, JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    # Bare body reference binds to the escaped parameter (not the same-named
    # global), for a plain function, an inner closure, and multiple parameters.
    @test run("@def_ctx_fn(ctxf1); ctxf1(41)") == 42
    @test run("@def_ctx_closure(ctxf2); ctxf2(41)") == 42
    @test run("@def_ctx_multi(ctxf3); ctxf3(40, 2)") == 42
    # Hygiene of a nested macro's identically-named reference is preserved.
    @test_throws UndefVarError run("@def_ctx_hygiene(ctxf4); ctxf4(41)")
    # READ-only: an assigned bare name is a fresh hygienic local, not the
    # escaped parameter; reading it before assignment throws.
    @test_throws UndefVarError run("@def_ctx_assign(ctxf5); ctxf5(41)")
    # READ-only: an explicit `local` declaration introduces a fresh local
    # rather than conflicting with (or resolving to) the escaped parameter.
    @test run("@def_ctx_local(ctxf6); ctxf6(41)") == 5
end

@testset "(AI) escaped parameter overlapped by `global` decl (known divergence)" begin
    # flisp resolves the bare name to the module global; JL errors on the
    # arg/global overlap (pre-existing divergence independent of the escaped-
    # parameter read alias, cf. "globals may overlap args" in test/scopes.jl).
    @test fl_eval(test_mod, JuliaSyntax.parsestmt(
        Expr, "@def_ctx_global(ctxf7fl); ctxf7fl(41)")) == 999
    @test_broken JuliaLowering.include_string(
        test_mod, "@def_ctx_global(ctxf7jl); ctxf7jl(41)";
        expr_compat_mode=true) == 999
    @test_broken JuliaLowering.include_string(
        test_mod, "@def_ctx_global(ctxf7jl2); ctxf7jl2(41)";
        expr_compat_mode=false) == 999
end

# Reverse of the escaped-parameter alias above: an old-style macro emits a
# keyword-argument *name* bare (its own layer) while esc'd defaults or the body
# reference it from the caller's (ancestor) layer.  flisp exempts keyword-arg
# names from hygiene renaming (macroexpand.scm `safe-llist-keyword-args`), so the
# esc'd reference binds to the kwarg; JuliaLowering must match this for
# flisp-compatible expansions.  This is the `Base.@kwdef` pattern (a field
# default `Expr(:kw, name, esc(defval))` referencing an earlier bare field).
fl_eval(test_mod, :(macro def_kw_body(fname)
    Expr(:function,
         Expr(:call, esc(fname), Expr(:parameters, :__kw__)),
         Expr(:block, esc(:(__kw__ + 1))))   # esc'd body binds to the kwarg
end))
fl_eval(test_mod, :(macro def_kw_closure(fname)
    Expr(:function,
         Expr(:call, esc(fname), Expr(:parameters, Expr(:kw, :__kw__, esc(4)))),
         Expr(:block, esc(:(inner() = __kw__ + 1)), esc(:(inner()))))
end))
fl_eval(test_mod, :(macro def_kw_default(fname)
    # esc'd default of `__kb__` references the earlier bare kwarg `__ka__`.
    Expr(:function,
         Expr(:call, esc(fname),
              Expr(:parameters, Expr(:kw, :__ka__, esc(2)),
                   Expr(:kw, :__kb__, esc(:(__ka__ * 10))))),
         Expr(:block, esc(:(__ka__ + __kb__))))
end))
fl_eval(test_mod, :(macro def_kw_shadow(fname)
    # kwarg name co-spelled with a caller-module global: the parameter wins.
    Expr(:function,
         Expr(:call, esc(fname), Expr(:parameters, Expr(:kw, :__kwsh__, esc(1)))),
         Expr(:block, esc(:__kwsh__)))
end))
fl_eval(test_mod, :(macro def_kw_assign(fname)
    # esc'd assignment to the kwarg name: read-only alias => fresh hygienic local
    # (see divergence testset), so the RHS read of the old value is undef.
    Expr(:function,
         Expr(:call, esc(fname), Expr(:parameters, Expr(:kw, :__kw__, esc(10)))),
         Expr(:block, esc(:(__kw__ = __kw__ + 5)), esc(:__kw__)))
end))
Base.eval(test_mod, :(global __kwsh__ = 999))
Core.@latestworld

@testset "(AI) keyword-argument name, escaped reference (flisp compat)" for run in [
    (x::String)->fl_eval(test_mod, JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    # esc'd body / inner-closure reference binds to the bare kwarg name.
    @test run("@def_kw_body(kwf1); kwf1(__kw__=41)") == 42
    @test run("@def_kw_closure(kwf2); kwf2(__kw__=41)") == 42
    @test run("@def_kw_closure(kwf2b); kwf2b()") == 5
    # esc'd default referencing an earlier kwarg (the @kwdef shape).
    @test run("@def_kw_default(kwf3); kwf3()") == 22
    @test run("@def_kw_default(kwf3b); kwf3b(__ka__=3)") == 33
    # kwarg parameter wins over a same-named caller global for reads.
    @test run("@def_kw_shadow(kwf4); kwf4()") == 1
    @test run("@def_kw_shadow(kwf4b); kwf4b(__kwsh__=7)") == 7
end

@testset "(AI) escaped assignment to a keyword-argument name (known divergence)" begin
    # flisp does not rename an *escaped* assigned name, so it mutates the kwarg
    # (reads the old value 10, stores 15); JuliaLowering keeps the alias
    # read-only (matching the escaped-parameter fix), so the assignment target is
    # a fresh hygienic local read before assignment -> UndefVarError.
    @test fl_eval(test_mod, JuliaSyntax.parsestmt(
        Expr, "@def_kw_assign(kwf5fl); kwf5fl()")) == 15
    @test_throws UndefVarError JuliaLowering.include_string(
        test_mod, "@def_kw_assign(kwf5jl); kwf5jl()"; expr_compat_mode=true)
    @test_throws UndefVarError JuliaLowering.include_string(
        test_mod, "@def_kw_assign(kwf5jl2); kwf5jl2()"; expr_compat_mode=false)
end

@testset "(AI) Base.@kwdef cross-referencing field default (flisp compat)" begin
    # `Base.@kwdef` emits `Expr(:kw, fieldname, esc(defval))`: bare field name,
    # esc'd default.  A default referencing an earlier field must resolve to it
    # (real-world: MadNLP `MadNLPOptions`).  Covers a plain and a parametric
    # struct; compares JuliaLowering (both syntax modes) against flisp.
    src = """
        module M
            Base.@kwdef struct Plain
                base::Int = 2
                derived::Int = base * 10
            end
            Base.@kwdef struct Param{T}
                a::T
                b::T = a + one(T)
            end
            results() = (Plain().derived, Plain(base=5).derived,
                         Param{Int}(a=3).b, Param{Float64}(a=1.5).b)
        end
    """
    mfl = Module(); Base.include_string(mfl, src); Core.@latestworld
    mjl = Module(); JuliaLowering.include_string(mjl, src; expr_compat_mode=true)
    Core.@latestworld
    mjl2 = Module(); JuliaLowering.include_string(mjl2, src; expr_compat_mode=false)
    Core.@latestworld
    @test mfl.M.results() == (20, 50, 4, 2.5)
    @test mjl.M.results() == mfl.M.results()
    @test mjl2.M.results() == mfl.M.results()
end

@testset "(AI) old-style macro method-def name -> macro-home global (flisp compat)" begin
    # An unescaped method-def *name* at the root of an old-style macro's
    # expansion binds a plain global of the *macro's* module (defining or
    # extending it), matching flisp -- not a mangled hygienic local.  A def
    # nested inside a block/quote keeps its hygienic renaming.  (Real-world:
    # Plots `@attributes`, RecipesBase `@recipe`.)  Compares JuliaLowering's
    # Expr-compat mode (the flisp round-trip path) against flisp.
    src = """
        module Mac
            macro identity_def(ex); ex; end
            existing(x) = "base"
        end
        module User
            using ..Mac
            Mac.@identity_def newf() = 1                    # (1) define in Mac
            Mac.@identity_def existing(x::Int) = "int"      # (2) extend Mac fn
            Mac.@identity_def begin blockf() = 2 end        # (3) nested -> local
        end
        results() = (Mac.newf(), Mac.existing(3), Mac.existing("s"),
                     isdefined(Mac, :blockf), isdefined(User, :blockf),
                     isdefined(User, :newf))
    """
    mfl = Module(); Base.include_string(mfl, src); Core.@latestworld
    mjl = Module(); JuliaLowering.include_string(mjl, src; expr_compat_mode=true)
    Core.@latestworld
    @test mfl.results() == (1, "int", "base", false, false, false)
    @test mjl.results() == mfl.results()

    # A method def emitted inside a function body is a global of the macro's
    # module, so (like flisp) it raises the top-level-only error rather than
    # silently becoming a local.
    @test_throws JuliaLowering.LoweringError JuliaLowering.include_string(
        Module(),
        "module M2; macro d(ex); ex; end; f() = @d(g()=1); end";
        expr_compat_mode=true)
end

@testset "(AI) @eval'd method-def payload extends eval-target global (flisp compat)" begin
    # A macro that relays its own argument to a nested `@eval` -- PETSc.jl's
    # `@for_libpetsc begin ... end` idiom, which generates per-scalar-type methods
    # for a type from a runtime list -- hands a block of method defs to a fresh
    # `eval()`.  flisp evaluates such a payload through an inert quote, stripping
    # the relaying macro's hygiene, so both a curly-form def (`T{S}(...)`, which
    # references the global type `T`) and a plain-form def (`T(...)`, an outer
    # constructor) in the same block extend the eval-target module's global `T`.
    # Previously the plain-form name became a spurious hygienic local, which the
    # curly-form def then read undefined: `UndefVarError: T@1 not defined in
    # local scope` (found via SafePETSc -> PETSc.jl in PkgEval).
    src = """
        macro relay(expr); quote; @eval \$expr; end; end
        mutable struct PCr{T}; ptr::Int; end
        @relay begin
            PCr{Float64}(comm::Bool) = PCr{Float64}(0)
            PCr(x::Vector{Float64}) = PCr{Float64}(0)
        end
        results() = (PCr{Float64}(true).ptr, PCr(Float64[1.0]).ptr)
    """
    # Compares JuliaLowering's Expr-compat mode (the flisp round-trip path, which
    # the old-style `@relay`/`@eval` expansion uses) against flisp.
    mfl = Module(); Base.include_string(mfl, src); Core.@latestworld
    mjl = Module(); JuliaLowering.include_string(mjl, src; expr_compat_mode=true)
    Core.@latestworld
    @test mfl.results() == (0, 0)
    @test mjl.results() == mfl.results()
end

@testset "(AI) @eval'd non-method payload binds eval-target globals (flisp compat)" begin
    # Companion to the method-def carve-out above: the same relay-to-`@eval` idiom
    # (PETSc's `@for_libpetsc`) also carries non-method definitions.  A re-evaluated
    # payload's unescaped top-scope `const` and plain-assignment targets bind plain
    # globals of the eval target, and unescaped references resolve there too -- flisp
    # evaluates the payload through an inert quote.  An *inline* hygienic expansion
    # keeps the mangling/locality (tested separately), so this is reeval-specific.
    same = """
        macro relay(expr); quote; @eval \$expr; end; end
        @relay begin
            const KC = 11
            ka = 22
            TA = Vector{Int}
        end
        results() = (KC, ka, TA)
    """
    mfl = Module(); Base.include_string(mfl, same); Core.@latestworld
    mjl = Module(); JuliaLowering.include_string(mjl, same; expr_compat_mode=true)
    Core.@latestworld
    @test mfl.results() == (11, 22, Vector{Int})
    @test mjl.results() == mfl.results()

    # Cross-module SafePETSc shape: the relaying macro lives in `Relayer`, but the
    # payload -- a `const` whose value references the *caller* module's own struct
    # `PooledVec` -- is written in `User`.  flisp binds the `const` in `User` and
    # resolves `PooledVec` to `User.PooledVec`; before the fix JuliaLowering read
    # `PooledVec` against `Relayer` (the macro's home), reproducing SafePETSc's
    # `UndefVarError: PooledVec not defined in PETSc`.
    cross = """
        module Relayer
            scalars = [Float64]
            macro for_scalar(expr)
                quote
                    for PetscScalar in scalars
                        @eval esc(\$expr)
                    end
                end
            end
        end
        module User
            using ..Relayer
            struct PooledVec{T}; n::Int; end
            Relayer.@for_scalar begin
                const VEC_POOL_Float64 = Dict{Int, Vector{PooledVec{Float64}}}()
            end
        end
        result() = valtype(typeof(User.VEC_POOL_Float64))
    """
    cfl = Module(); Base.include_string(cfl, cross); Core.@latestworld
    cjl = Module(); JuliaLowering.include_string(cjl, cross; expr_compat_mode=true)
    Core.@latestworld
    @test cfl.result() == Vector{cfl.User.PooledVec{Float64}}
    @test cjl.result() == Vector{cjl.User.PooledVec{Float64}}
end

# Wholesale port of flisp's expansion-environment identity mapping
# (macroexpand.scm `keywords-introduced-by`/`safe-llist-keyword-args`): the
# escaped-argument-name alias applies to every argument-name position of a
# *named* method definition -- destructured (tuple) components, optional-arg
# names, varargs, rest kwargs -- and to nothing else: anonymous functions,
# `->`, `do` blocks, generators, macro definitions, and the self name of a
# callable-object definition get no identity mapping in flisp, so their
# escaped names must NOT alias bare same-named body references (which resolve
# as macro-home-module globals instead).

# Aliased: escaped names in every arg-name position of a named def.
fl_eval(test_mod, :(macro def_destr_fn(fname)
    quote
        function $(esc(fname))(($(esc(:__da__)), b))
            return __da__ + b       # bare ref binds the destructured element
        end
    end
end))
fl_eval(test_mod, :(macro def_destr_short(fname)
    quote
        $(esc(fname))(($(esc(:__da__)), b)) = __da__ + b
    end
end))
fl_eval(test_mod, :(macro def_destr_nested(fname)
    quote
        function $(esc(fname))((($(esc(:__da__)), b), c))
            return __da__ + b + c
        end
    end
end))
fl_eval(test_mod, :(macro def_opt_arg(fname)
    p = Expr(:kw, esc(:__oa__), 40)
    quote
        function $(esc(fname))($p)
            return __oa__ + 2
        end
    end
end))
fl_eval(test_mod, :(macro def_va_arg(fname)
    quote
        function $(esc(fname))($(esc(:__va__))...)
            return sum(__va__)
        end
    end
end))
fl_eval(test_mod, :(macro def_esc_kwname(fname)
    p = Expr(:kw, esc(:__ek__), 1)
    quote
        function $(esc(fname))(; $p)
            return __ek__ + 1       # bare body ref binds the esc'd kwarg
        end
    end
end))
fl_eval(test_mod, :(macro def_esc_restkw(fname)
    p = Expr(:..., esc(:__rk__))
    quote
        function $(esc(fname))(; $p)
            return length(__rk__)
        end
    end
end))
# NOT aliased: `->`, `do`, generators, and the callable-object self name.
# flisp resolves the bare body reference as a global of the macro's home
# module (here `test_mod`), so the planted 999-valued globals below are read.
fl_eval(test_mod, :(macro mk_arrow()
    :($(esc(:__na__)) -> __na__ + 1)
end))
fl_eval(test_mod, :(macro mk_do(f)
    quote
        $(esc(f))() do $(esc(:__na__))
            __na__ + 1
        end
    end
end))
fl_eval(test_mod, :(macro mk_gen()
    :(collect(__ng__ + 1 for $(esc(:__ng__)) in [5]))
end))
fl_eval(test_mod, :(macro def_esc_self(tname)
    quote
        function ($(esc(:__ns__))::$(esc(tname)))()
            return __ns__          # NOT the callable object: macro-home global
        end
    end
end))
Base.eval(test_mod, :(global __da__ = 999))
Base.eval(test_mod, :(global __oa__ = 999))
Base.eval(test_mod, :(global __va__ = 999))
Base.eval(test_mod, :(global __ek__ = 999))
Base.eval(test_mod, :(global __rk__ = 999:999))
Base.eval(test_mod, :(global __na__ = 999))
Base.eval(test_mod, :(global __ng__ = 999))
Base.eval(test_mod, :(global __ns__ = 999))
Base.eval(test_mod, :(struct SelfCB1 end))
Base.eval(test_mod, :(callf(g) = g(41)))
Core.@latestworld

@testset "(AI) escaped arg names: named-def positions alias, others don't (flisp compat)" for run in [
    (x::String)->fl_eval(test_mod, JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    # Destructured argument components (function form, `=` short form, nested
    # tuple): the bare body reference binds the escaped element, not the
    # same-named macro-home global (999).
    @test run("@def_destr_fn(daf1); daf1((40, 2))") == 42
    @test run("@def_destr_short(daf2); daf2((40, 2))") == 42
    @test run("@def_destr_nested(daf3); daf3(((40, 1), 1))") == 42
    # Optional-arg name, vararg name, escaped kwarg name, escaped rest-kwarg.
    @test run("@def_opt_arg(oaf1); oaf1()") == 42
    @test run("@def_opt_arg(oaf2); oaf2(7)") == 9
    @test run("@def_va_arg(vaf1); vaf1(40, 2)") == 42
    @test run("@def_esc_kwname(ekf1); ekf1(__ek__ = 41)") == 42
    @test run("@def_esc_restkw(rkf1); rkf1(a = 1, b = 2)") == 2
    # No identity mapping for `->`/`do`/generator escaped "args": the bare
    # body reference reads the macro-home global (999), like flisp.
    @test run("(@mk_arrow())(41)") == 1000
    @test run("@mk_do(callf)") == 1000
    @test run("@mk_gen()") == [1000]
    # No identity mapping for an escaped callable-object self name.
    @test run("@def_esc_self(SelfCB1); SelfCB1()()") == 999
end

# flisp's identity mapping leaves the name as a *raw symbol*, so a reference to
# an identity-mapped name (an esc'd named-def argument, or a keyword-arg name)
# is subject to ordinary lexical shadowing by any intervening binder that flisp
# also leaves as the raw symbol -- e.g. an esc'd `->`/`do`/generator argument
# or an esc'd `let` binding of the same name.  Those binders carry a different
# scope layer here, so the alias/binding must yield to them (raw-symbol
# shadowing in `resolve_name`), while a bare binder belonging to an unrelated
# nested expansion (which flisp gensym-renames) must not capture.
fl_eval(test_mod, :(macro def_shadow_do(fname)
    quote
        function $(esc(fname))($(esc(:__sh__)))
            map([2]) do $(esc(:__sh__))
                __sh__ + 1         # binds the do-arg, not the outer argument
            end
        end
    end
end))
fl_eval(test_mod, :(macro def_shadow_arrow(fname)
    quote
        function $(esc(fname))($(esc(:__sh__)))
            ($(esc(:__sh__)) -> __sh__ + 1)(2)
        end
    end
end))
fl_eval(test_mod, :(macro def_shadow_gen(fname)
    quote
        function $(esc(fname))($(esc(:__sh__)))
            collect(__sh__ for $(esc(:__sh__)) in [1, 2, 3])
        end
    end
end))
fl_eval(test_mod, :(macro def_shadow_let(fname)
    quote
        function $(esc(fname))($(esc(:__sh__)))
            let $(esc(:__sh__)) = 2
                __sh__ + 1
            end
        end
    end
end))
fl_eval(test_mod, :(macro def_shadow_kw(fname)
    # bare kwarg name: identity-mapped even unescaped, so both the esc'd and
    # the bare reference in the arrow body bind the esc'd arrow argument.
    quote
        function $(esc(fname))(; __sh__ = 40)
            ($(esc(:__sh__)) -> $(esc(:__sh__)) + __sh__)(2)
        end
    end
end))
# Splicing guard: the outer identity-mapped reference is passed into a nested
# macro whose arrow binder is esc'd; that esc resolves to the outer macro's
# layer -- the same raw symbol -- so it shadows there too, exactly as flisp.
fl_eval(test_mod, :(macro shadow_inner_fn(body)
    :(($(esc(:__sh__)) -> $(esc(body)))(2))
end))
fl_eval(test_mod, :(macro def_shadow_nested(fname)
    quote
        function $(esc(fname))($(esc(:__sh__)))
            @shadow_inner_fn(__sh__ + 1)
        end
    end
end))
Base.eval(test_mod, :(global __sh__ = 999))
Core.@latestworld

@testset "(AI) identity-mapped names are raw-symbol shadowable (flisp compat)" for run in [
    (x::String)->fl_eval(test_mod, JuliaSyntax.parsestmt(Expr, "#=FLISP SANITY-CHECK=# "*x)),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL COMPAT=# "*x; expr_compat_mode=true),
    (x::String)->JuliaLowering.include_string(
        test_mod, "#=JL=# "*x; expr_compat_mode=false)]

    # An esc'd inner binder shadows the aliased outer esc'd argument (do,
    # arrow, generator, let); without raw-symbol shadowing these would read
    # the outer argument instead (41, 41, [10,10,10], 41).
    @test run("@def_shadow_do(shf1); shf1(40)") == [3]
    @test run("@def_shadow_arrow(shf2); shf2(40)") == 3
    @test run("@def_shadow_gen(shf3); shf3(10)") == [1, 2, 3]
    @test run("@def_shadow_let(shf4); shf4(40)") == 3
    # A bare kwarg name is identity-mapped too: an intervening esc'd arrow
    # argument shadows it for bare references as well (2 + 2, not 2 + 40).
    @test run("@def_shadow_kw(shf5); shf5()") == 4
    # Nested-expansion splice: the nested macro's esc'd binder is the outer
    # layer's raw symbol and captures the spliced reference (2 + 1).
    @test run("@def_shadow_nested(shf6); shf6(40)") == 3
end

@testset "(AI) old-style macro-in-macro: name binds macro-home global (flisp compat)" begin
    # flisp resolves a macro-definition *name* in a hygienic expansion like any
    # bare reference -- a plain global of the macro's home module, at any
    # nesting depth (macroexpand.scm has no binding pattern for `macro`) -- so
    # a macro-generated macro lands in (and is callable from) the generating
    # macro's module.  Macro *arguments*, however, get no identity mapping
    # (flisp treats `macro` like `->`), so an escaped inner-macro argument
    # does not alias a bare body reference.
    src = """
        module Mac
            macro mkmac()
                :(macro genm(); 42; end)
            end
            macro mkmac_nested()
                quote
                    begin
                        macro genn(); 43; end
                    end
                    nothing
                end
            end
        end
        module User
            using ..Mac
            Mac.@mkmac
            Mac.@mkmac_nested
        end
        results() = (Mac.@genm(), Mac.@genn(),
                     isdefined(Mac, Symbol("@genm")), isdefined(User, Symbol("@genm")),
                     isdefined(Mac, Symbol("@genn")), isdefined(User, Symbol("@genn")))
    """
    # Compares JuliaLowering's Expr-compat mode (the flisp round-trip path)
    # against flisp; in non-compat mode `@mkmac` is a *new-style* macro whose
    # Expr return value is rejected up front (a deliberate, separate
    # restriction), so there is nothing to compare there.
    mfl = Module(); Base.include_string(mfl, src); Core.@latestworld
    mjl = Module(); JuliaLowering.include_string(mjl, src; expr_compat_mode=true)
    Core.@latestworld
    @test mfl.results() == (42, 43, true, false, true, false)
    @test mjl.results() == mfl.results()
end
