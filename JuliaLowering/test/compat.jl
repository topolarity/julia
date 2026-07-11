test_mod = Module()

const JL_DIR = joinpath(@__DIR__, "..")

# copied from JuliaSyntax/test/parse_packages.jl
function find_source_in_path(basedir)
    src_list = String[]
    for (root, _dirs, files) in walkdir(basedir)
        append!(src_list, (joinpath(root, f) for f in files
                               if endswith(f, ".jl") && (p = joinpath(root,f); !islink(p) && isfile(p))))
    end
    src_list
end

function find_diff(e1, e2, loc=Ref(LineNumberNode(0)))
    if expr_equal_forgiving(e1, e2)
        return nothing, nothing
    elseif !(e1 isa Expr && e2 isa Expr) ||
        e1.head !== e2.head ||
        length(e1.args) !== length(e2.args)
        return (e1, e2), (loc[])
    else
        for i in 1:length(e1.args)
            e1.args[i] isa LineNumberNode && (loc[] = e1.args[i])
            (diff, path) = find_diff(e1.args[i], e2.args[i], loc)
            isnothing(diff) || return (diff, (e1.head, i, path))
        end
    end
end

function test_each_in_path(test_f::Function, basedir)
    ran = 0
    for filepath in find_source_in_path(basedir)
        @testset "$(relpath(filepath, basedir))" begin
            str = try
                read(filepath, String)
            catch
                continue
            end
            ran += test_f(str)
        end
    end
    @test ran > 0
    nothing
end

# ignore_linenums=false is good for checking, but too noisy to use much
function expr_equal_forgiving(e1, e2; ignore_linenums=true)
    !(e1 isa Expr && e2 isa Expr) && return e1 == e2
    if ignore_linenums
        e1, e2 = let e1b = Expr(e1.head), e2b = Expr(e2.head)
            e1b.args = filter(x->!(x isa LineNumberNode), e1.args)
            e2b.args = filter(x->!(x isa LineNumberNode), e2.args)
            e1b, e2b
        end
    end

    e1.head === e2.head && length(e1.args) === length(e2.args) &&
        all(expr_equal_forgiving(a1, a2; ignore_linenums) for (a1, a2) in
                zip(e1.args, e2.args))
end

@testset "Expr<->EST" begin
    function roundtrip(e)
        JuliaLowering.est_to_expr(JuliaLowering.expr_to_est(e))
    end
    function roundtrip_eq(str)
        e_ref = try
            JuliaSyntax.parseall(Expr, str)
        catch _
            nothing
        end
        isnothing(e_ref) && return 0
        e_test = roundtrip(e_ref)
        pass = expr_equal_forgiving(e_test, e_ref)
        @test pass
        if !pass
            ((e_ref_min, e_test_min), indices) = find_diff(e_ref, e_test)
            @info "diff:" e_ref_min e_test_min indices # e_ref e_test
        end
        return 1
    end

    local expr_syntax = Any[
        LineNumberNode(1)
        :foo
        Expr(:foo, 1)
        GlobalRef(Core, :nothing)
        nothing
    ]

    local expr_wrappers = Function[
        identity
        x->QuoteNode(x)
        x->Expr(:function, x)
        x->Expr(:dummy, x)
    ]

    # TODO: `@ast_` escaping is broken
    unused = JuliaSyntax.parsestmt(JuliaSyntax.SyntaxTree, "foo")
    JuliaLowering.ensure_macro_attributes!(unused._graph)
    local st_wrappers = Function[
        x->(@ast unused._graph unused (x::K"Value"))
        x->(@ast unused._graph unused [K"inert" x::K"Value"])
        x->(@ast unused._graph unused [K"function" x::K"Value"])
    ]

    @testset "every basic case" begin
        for e in expr_syntax, w1 in expr_wrappers, w2 in expr_wrappers
            e_wrapped = w2(w1(e))
            @test roundtrip(e_wrapped) == e_wrapped
        end

        for e in expr_syntax, st_w in st_wrappers, e_w in expr_wrappers
            e_wrapped = st_w(e_w(e))
            @test roundtrip(e_wrapped) == e_wrapped
            e_wrapped = e_w(st_w(e))
            @test roundtrip(e_wrapped) == e_wrapped
        end
    end

    @testset "special cases: Value implicitly quotes AST nodes" begin
        @test JL.est_to_expr(@ast_ :foo::K"Value") ==
            JL.est_to_expr(@ast_ [K"inert" "foo"::K"Identifier"]) ==
            QuoteNode(:foo)
        @test JL.est_to_expr(@ast_ Expr(:call, 1)::K"Value") ==
            JL.est_to_expr(@ast_ [K"inert" [K"call" 1::K"Value"]]) ==
            QuoteNode(Expr(:call, 1))
        @test JL.est_to_expr(@ast_ QuoteNode(Expr(:call, 1))::K"Value") ==
            JL.est_to_expr(@ast_ [K"inert" [K"inert" [K"call" 1::K"Value"]]]) ==
            QuoteNode(QuoteNode(Expr(:call, 1)))
    end

    @testset "provenance via scavenging for LineNumberNodes" begin
        # Provenance of a node should generally be the last seen
        # LineNumberNode in the depth-first traversal of the Expr, or the
        # initial line given if none have been seen yet.  If none have been seen
        # and no initial line was given, .source should still be defined on all
        # nodes (of unspecified value, but hopefully a helpful value for the
        # user.)

        ex = Expr(:block,
                  LineNumberNode(123),
                  Expr(:block,
                       Expr(:block, LineNumberNode(456)),
                       Expr(:block)),
                  Expr(:block,
                       Expr(:block),
                       Expr(:block)))

        # No initial line provided
        st = JuliaLowering.expr_to_est(ex)
        for i in length(st._graph.edge_ranges)
            @test !isnothing(get(SyntaxTree(st._graph, i), :source, nothing))
        end
        @test let lnn = st[1].source;    lnn isa LineNumberNode && lnn.line === 123; end
        @test let lnn = st[1][1].source; lnn isa LineNumberNode && lnn.line === 123; end
        @test let lnn = st[1][2].source; lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2].source;    lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2][1].source; lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2][2].source; lnn isa LineNumberNode && lnn.line === 456; end

        # Same tree, but provide an initial line
        st = JuliaLowering.expr_to_est(ex, LineNumberNode(789))
        @test let lnn = st.source;       lnn isa LineNumberNode && lnn.line === 789; end
        @test let lnn = st[1].source;    lnn isa LineNumberNode && lnn.line === 123; end
        @test let lnn = st[1][1].source; lnn isa LineNumberNode && lnn.line === 123; end
        @test let lnn = st[1][2].source; lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2].source;    lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2][1].source; lnn isa LineNumberNode && lnn.line === 456; end
        @test let lnn = st[2][2].source; lnn isa LineNumberNode && lnn.line === 456; end

        ex = parsestmt(Expr, """
        begin
            try
                maybe
                lots
                of
                lines
            catch exc
                y
            end
        end""")
        st = JuliaLowering.expr_to_est(ex, LineNumberNode(1))

        # sanity: ensure we're testing the tree we expect
        @test st ≈ @ast_ [K"block"
            [K"try"
                [K"block"
                    "maybe"::K"Identifier"
                    "lots"::K"Identifier"
                    "of"::K"Identifier"
                    "lines"::K"Identifier"
                ]
                "exc"::K"Identifier"
                [K"block" "y"::K"Identifier"]
            ]
        ]

        @test let lnn = st.source;             lnn isa LineNumberNode && lnn.line === 1; end
        @test let lnn = st[1].source;          lnn isa LineNumberNode && lnn.line === 2; end
        @test let lnn = st[1][1].source;       lnn isa LineNumberNode && lnn.line === 2; end
        @test let lnn = st[1][1][1].source;    lnn isa LineNumberNode && lnn.line === 3; end
        @test let lnn = st[1][1][2].source;    lnn isa LineNumberNode && lnn.line === 4; end
        @test let lnn = st[1][1][3].source;    lnn isa LineNumberNode && lnn.line === 5; end
        @test let lnn = st[1][1][4].source;    lnn isa LineNumberNode && lnn.line === 6; end
        @test let lnn = st[1][2].source;       lnn isa LineNumberNode && lnn.line === 6; end
        @test let lnn = st[1][3].source;       lnn isa LineNumberNode && lnn.line === 6; end
        @test let lnn = st[1][3][1].source;    lnn isa LineNumberNode && lnn.line === 8; end

        st_shortfunc = JuliaLowering.expr_to_est(
            Expr(:block,
                 LineNumberNode(11),
                 Expr(:(=),
                      Expr(:call, :f),
                      :body))
        )
        @test st_shortfunc ≈ @ast_ [K"block"
            [K"="
                [K"call" "f"::K"Identifier"]
                "body"::K"Identifier"
            ]
        ]
        @test let lnn = st_shortfunc[1][1].source; lnn isa LineNumberNode && lnn.line === 11; end

        st_shortfunc_2 = JuliaLowering.expr_to_est(
            Expr(:block,
                 LineNumberNode(11),
                 Expr(:(=),
                      Expr(:call, :f),
                      Expr(:block,
                           LineNumberNode(22),
                           :body)))
        )
        @test st_shortfunc_2 ≈ @ast_ [K"block"
            [K"="
                [K"call" "f"::K"Identifier"]
                [K"block" "body"::K"Identifier"]
            ]
        ]
        @test let lnn = st_shortfunc_2[1][1].source; lnn isa LineNumberNode && lnn.line === 22; end
    end

    @testset "linenodes equal (modules and functions have extra)" begin
        e = JuliaSyntax.parseall(Expr, """
        module M
        function f()
            if x
                j
            elseif y
                let
                    y
                end
            end
        end
        begin
            1
        end
        end
        """; filename="foo")
        @test e == roundtrip(e)
    end

    @testset "bulk parsed code, no linenodes" begin
        test_each_in_path(roundtrip_eq, JL_DIR)
    end

    @testset "Base.@__doc__ marker block shape" begin
        # From PkgEval: Unitful (@refunit / @prefixed_unit_symbols nested @__doc__); 12+ dependents failed via it
        # `Base.@__doc__` expands to `(block (meta doc) x)`, which
        # `Base.Docs.finddoc` recognizes only via `isexpr(def, :block, 2) &&
        # isexpr(def.args[1], :meta, 1)`.  `est_to_expr` must therefore not
        # synthesize provenance `LineNumberNode`s into this block, or the
        # length-2 match breaks and documenting a macrocall whose expansion
        # nests another `@__doc__` fails with "cannot document ...".
        marker = Expr(:block, Expr(:meta, :doc), :(const global z = 1))
        is_marker(e) = Base.isexpr(e, :block, 2) &&
            Base.isexpr(e.args[1], :meta, 1) && e.args[1].args[1] === :doc

        @test is_marker(roundtrip(marker))
        # Idempotent across repeated round trips (nested @__doc__ resolution
        # re-converts the same subtree multiple times).
        @test is_marker(roundtrip(roundtrip(roundtrip(marker))))
        # The marker keeps its shape when embedded behind other structure, as
        # produced by an outer `@__doc__` wrapping a macrocall (finddoc
        # tolerates the extra line nodes on the ancestor blocks, but the marker
        # itself must stay exactly length 2).
        for wrap in (x->Expr(:block, x),
                     x->Expr(:escape, Expr(:block, x)),
                     x->Expr(:block, :(y = 2), x))
            e = roundtrip(wrap(marker))
            found = Ref(false)
            find_marker(x) = x isa Expr &&
                (is_marker(x) ? (found[] = true) : foreach(find_marker, x.args))
            find_marker(e)
            @test found[]
        end
    end
end

# taken from JuliaSyntax expr.jl
test_programs = [
    "begin a\nb\n\nc\nend",
    "(a;b;c)",
    "begin end",
    "(;;)",
    "a;b",
    "module A\n\nbody\nend",
    "function f()\na\n\nb\nend",
    "f() = 1",
    "macro f()\na\nend",
    "function f end",
    "macro f end",
    "function (f() where {T}) end",
    "function (f()::S) end",
    "a -> b",
    "(a,) -> b",
    "(a where {T}) -> b",
    "a -> (\nb;c)",
    "a -> begin\nb\nc\nend",
    "(a;b=1) -> c",
    "(a...;b...) -> c",
    "(;) -> c",
    "a::T -> b",
    "let i=is, j=js\nbody\nend",
    "for x=xs\n\nend",
    "for x=xs\ny\nend",
    "while cond\n\nend",
    "while cond\ny\nend",
    "f() = xs",
    "f() =\n(a;b)",
    "f() =\nbegin\na\nb\nend",
    "let f(x) =\ng(x)=1\nend",
    "f() .= xs",
    "for i=is body end",
    "for i=is, j=js\nbody\nend",
    "f(x) do y\n body end",
    "@f(x) do y body end",
    "f(x; a=1) do y body end",
    "g(f(x) do y\n body end)",
    "f(a=1)",
    "f(; b=2)",
    "f(a=1; b=2)",
    "f(a; b; c)",
    "+(a=1,)",
    "(a=1)()",
    "(x=1) != 2",
    "+(a=1)",
    "(a=1)'",
    "f.(a=1; b=2)",
    "(a=1,)",
    "(a=1,; b=2)",
    "(a=1,; b=2; c=3)",
    "x[i=j]",
    "(i=j)[x]",
    "x[a, b; i=j]",
    "(i=j){x}",
    "x{a, b; i=j}",
    "[a=1,; b=2]",
    "{a=1,; b=2}",
    "f(a .= 1)",
    "f(((a = 1)))",
    "(((a = 1)),)",
    "(;((a = 1)),)",
    "(a = 1) |> f",
    "(a = 1)'",
    "a.b",
    "a.@b x",
    "f.(x,y)",
    "f.(x=1)",
    "f.(a=1; b=2)",
    "(a=1).()",
    "x .+ y",
    "(x=1) .+ y",
    "a .< b .< c",
    "a .< (.<) .< c",
    "quote .+ end",
    ".+(x)",
    ".+x",
    "f(.+)",
    "(a, .+)",
    "x += y",
    "x .+= y",
    "x \u2212= y",
    "let x=1\n end",
    "let x=1 ; end",
    "let x ; end",
    "let x::1 ; end",
    "let x=1,y=2 end",
    "let x+=1 ; end",
    "let ; end",
    "let ; body end",
    "let\na\nb\nend",
    "A where {T}",
    "A where {S, T}",
    "A where {X, Y; Z}",
    "@m\n",
    "\n@m",
    "@m(x; a)",
    "@m(a=1; b=2)",
    "@S[a,b]",
    "@S[a b]",
    "@S[a; b]",
    "@S[a ;; b]",
    "[x,y ; z]",
    "[a ;;; b ;;;; c]",
    "[a b ; c d]",
    "[a\nb]",
    "[a b]",
    "[a b ; c d]",
    "T[a ;;; b ;;;; c]",
    "T[a b ; c d]",
    "T[a\nb]",
    "T[a b]",
    "T[a b ; c d]",
    "(x for a in as for b in bs)",
    "(x for a in as, b in bs)",
    "(x for a in as, b in bs if z)",
    "(x for a in as, b in bs for c in cs, d in ds)",
    "(x for a in as for b in bs if z)",
    "(x for a in as if z for b in bs)",
    "[x for a = as for b = bs if cond1 for c = cs if cond2]" ,
    "[x for a = as if begin cond2 end]" ,
    "(x for a in as if z)",
    "return x",
    "struct A end",
    "mutable struct A end",
    "struct A <: B \n a::X \n end",
    "struct A \n a \n b \n end",
    "struct A const a end",
    "export a",
    "export +, ==",
    "export \n a",
    "global x",
    "local x",
    "global x,y",
    "const x,y = 1,2",
    "const x = 1",
    "global x ~ 1",
    "global x += 1",
    "(;)",
    "(; a=1)",
    "(; a=1; b=2)",
    "(a; b; c,d)",
    "module A end",
    "baremodule A end",
    "import A",
    "A.x",
    "A.\$x",
    "try x catch e; y end",
    "try x finally y end",
    "try x catch e; y finally z end",
    "try x catch e; y else z end",
    "try x catch e; y else z finally w end",
    "..",
    "a..b",
    "..(a)",
    "..(..,..)",
    "@.",
    "@..",
    "@..."
]
test_toplevel_programs = [
    "\"docstr\"\nthing_to_be_documented",
]

@testset "Test RawGreenNode->EST->Expr against RawGreenNode->Expr" begin
    function test_est(str; rule=:all, test_validator=true)
        parse = rule === :all ? JS.parseall : JS.parsestmt
        e_ref = try
            parse(Expr, str)
        catch _
            nothing
        end
        isnothing(e_ref) && return 0
        est_test = parse(SyntaxTree, str)
        e_test = JL.est_to_expr(est_test)
        pass = expr_equal_forgiving(e_test, e_ref)
        @test pass
        if !pass
            ((e_ref_min, e_test_min), indices) = find_diff(e_ref, e_test)
            @info "diff:" e_ref_min e_test_min indices # e_ref e_test
        end

        # test the validator
        test_validator && @test JL.valid_st0(est_test)
        return 1
    end

    @testset "snippets" begin
        for p in test_programs
            test_est(p; rule=:statement, test_validator=false)
        end
        for p in test_toplevel_programs
            test_est(p; test_validator=false)
        end
    end

    @testset "bulk parsed code, no linenodes" begin
        test_each_in_path(test_est, JL_DIR)

        basedir = joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "base")
        test_each_in_path(test_est, basedir)

        base_testdir = joinpath(Sys.BINDIR, Base.DATAROOTDIR, "julia", "test")
        test_each_in_path(test_est, base_testdir)

        @testset "Parse Julia stdlib at $(Sys.STDLIB)" begin
            for stdlib in readdir(Sys.STDLIB)
                fulldir = joinpath(Sys.STDLIB, stdlib)
                if isdir(fulldir)
                    test_each_in_path(test_est, joinpath(Sys.STDLIB, fulldir))
                end
            end
        end

    end

    @testset "test exceptions to blocks containing linenodes" begin
        # Macro authors are otherwise expected to handle LineNumberNode in
        # blocks, but since they were never emitted in `let` or `for` assignment
        # blocks, test that we have the same behaviour.
        @testset "linenodes equal in `let`" begin
            s = """
            let a=1, b=2, c=3
                a,b,c
            end
            """
            @test JL.est_to_expr(JS.parsestmt(SyntaxTree, s)) == JS.parsestmt(Expr, s)
        end
        @testset "linenodes equal in `for`" begin
            s = """
            for a in 1:2, b in 3:4, c in 5:6
                a,b,c
            end
            """
            @test JL.est_to_expr(JS.parsestmt(SyntaxTree, s)) == JS.parsestmt(Expr, s)
        end
    end
end

@testset "non-ASCII operator handling" begin
    # regression test for invalid string index
    @test JuliaLowering.include_string(test_mod, raw"""
    @noinline (x = 0xF; x ⊻= 1; x)
    """; expr_compat_mode=true) == 0xE
end

@testset "Expr(:ssavalue) conversion" begin
    # Expr(:ssavalue, N) should be converted to [K"ssavalue" N::K"Value"]
    st = JuliaLowering.expr_to_est(Expr(:ssavalue, 0))
    @test kind(st) === K"ssavalue"
    @test st[1].value == 0

    st = JuliaLowering.expr_to_est(Expr(:ssavalue, 42))
    @test kind(st) === K"ssavalue"
    @test st[1].value == 42

    # Roundtrip: ssavalue should convert back to Expr(:ssavalue, N)
    @test JL.est_to_expr(JuliaLowering.expr_to_est(Expr(:ssavalue, 5))) ==
        Expr(:ssavalue, 5)

    # ssavalue references inside a lambda body should lower successfully
    lambda = Expr(:lambda, Any[:x],
        Expr(:block,
            Expr(:(=), Expr(:ssavalue, 0), Expr(:call, GlobalRef(Core, :typeof), :x)),
            Expr(:return, Expr(:ssavalue, 0))))
    out = JL.core_lowering_hook(lambda, test_mod)
    @test out isa Core.SimpleVector && out[1] isa Core.CodeInfo
end

@testset "bare `elseif` Expr == independent `if` (flisp parity)" begin
    # From PkgEval: DynamicSumTypes v3.7.5, src/DynamicSumTypes.jl:117-125 branchs() spliced at :58 (@sumtype)
    # flisp maps `elseif` to the same `expand-if` handler as `if`, so an
    # `Expr(:elseif, ...)` that is NOT nested in the else-slot of a preceding
    # `if`/`elseif` (e.g. spliced as a sibling statement in a `block`, as
    # DynamicSumTypes' `@sumtype` macro does via a flat `Vector{Expr}`) is
    # accepted and behaves exactly like a standalone `if` -- its own condition,
    # its own body, evaluated in sequence and NOT chained to any earlier `if`.

    # A bare `elseif` becomes `K"if"`; a nested else-slot `elseif` stays `K"elseif"`.
    @test kind(JuliaLowering.expr_to_est(Expr(:elseif, :c, :t))) === K"if"
    let st = JuliaLowering.expr_to_est(Expr(:if, :c1, :t1, Expr(:elseif, :c2, :t2)))
        @test kind(st) === K"if"
        @test kind(st[3]) === K"elseif"          # chain preserved byte-identically
    end
    # An `elseif` in a block sibling position is bare, even at arg 3 of the block.
    let st = JuliaLowering.expr_to_est(Expr(:block, :s1, :s2, Expr(:elseif, :c, :t)))
        @test kind(st[3]) === K"if"
    end
    # Chained `elseif` inside a bare (block-sibling) `elseif` stays a chain.
    let st = JuliaLowering.expr_to_est(
                Expr(:block, Expr(:elseif, :c1, :t1, Expr(:elseif, :c2, :t2))))
        @test kind(st[1]) === K"if"
        @test kind(st[1][3]) === K"elseif"
    end

    # End-to-end: the exact flat/sibling shape DynamicSumTypes.jl builds --
    # `[Expr(:if,...), Expr(:elseif,...), ...]` spliced as block siblings.
    branches = Any[
        Expr(:if,     :(v isa Int),     :(return 1)),
        Expr(:elseif, :(v isa Float64), :(return 2)),
        Expr(:elseif, :(v isa String),  :(return 3)),
    ]
    fdef = Expr(:function, :(f_bare_elseif(v)),
                Expr(:block, branches..., :(error("unreachable"))))
    jl_eval(test_mod, fdef)
    f = getfield(test_mod, :f_bare_elseif)
    @test Base.invokelatest(f, 1) == 1
    @test Base.invokelatest(f, 1.0) == 2
    @test Base.invokelatest(f, "x") == 3

    # flisp parity: each bare `elseif` is INDEPENDENT, not chained.  With an
    # intervening statement between the `if` and a following `elseif` sibling,
    # both branches run on their own conditions (proving no real if/elseif
    # dispatch -- see notes) rather than only one being selected.
    gdef = Expr(:function, :(g_bare_elseif(v)),
                Expr(:block,
                    Expr(:if, :(v == 1), :(push!(log, :a))),
                    :(push!(log, :mid)),
                    Expr(:elseif, :(v == 1), :(push!(log, :b))),
                    :(return log)))
    jl_eval(test_mod, :(log = Symbol[]))
    jl_eval(test_mod, gdef)
    g = getfield(test_mod, :g_bare_elseif)
    @test Base.invokelatest(g, 1) == [:a, :mid, :b]
end

@testset "pre-built `kw` node in `->`/`function` arglist (Dagger `@spawn`)" begin
    # From PkgEval: Dagger v0.19.4, src/thunk.jl:471 (@spawn f(A; kw=v) do-block splices Expr(:kw) into closure params)
    # A macro that captures a call's keyword arg as an `Expr(:kw, name, val)`
    # and splices it into a forwarding closure's parameter list (Dagger's
    # `@spawn f(A; dims=1) do ... end` builds `(A; dims=1) -> ...`) yields a
    # `(block <positional> (kw name val))` lambda arglist.  Text parsing of
    # `(A; dims=1)` gives an `=`-shaped kwarg node, but the spliced node stays
    # `kw`-shaped; both spellings must lower identically and match flisp.
    K(name, val) = Expr(:kw, name, val)
    tup(xs...) = Expr(:tuple, xs...)
    norm(ir) = replace(strip(sprint(JL.print_ir, ir)), r"#+\d+" => "#N")

    kw_lam = Expr(:->, Expr(:block, :A, K(:dims, 1)), tup(:A, :dims))
    eq_lam = Expr(:->, Expr(:block, :A, Expr(:(=), :dims, 1)), tup(:A, :dims))

    # The `kw` and `=` spellings lower to byte-identical IR (`#N` normalizes the
    # per-session closure-gensym counter).
    @test norm(jl_lower(test_mod, kw_lam; expr_compat_mode=true)) ==
          norm(jl_lower(test_mod, eq_lam; expr_compat_mode=true))

    for lam in (kw_lam, eq_lam)
        f = jl_eval(test_mod, lam; expr_compat_mode=true)
        @test Base.invokelatest(f, 10) === (10, 1)
        @test Base.invokelatest(f, 10; dims=2) === (10, 2)
        # flisp parity of the observable call behavior.
        g = fl_eval(test_mod, lam)
        @test Base.invokelatest(g, 10) === (10, 1)
        @test Base.invokelatest(g, 10; dims=2) === (10, 2)
    end

    # The anonymous-`function` head routes through the same validator arm.
    kw_fn = Expr(:function, Expr(:block, :A, K(:dims, 1)), tup(:A, :dims))
    h = jl_eval(test_mod, kw_fn; expr_compat_mode=true)
    @test Base.invokelatest(h, 10) === (10, 1)
    @test Base.invokelatest(h, 10; dims=2) === (10, 2)
end

@testset "qualified operator in comparison chain (Tullio `@fastmath` rewrite)" begin
    # From PkgEval: PolaronMobility v2.0.1, src/MobilityTheories.jl:377 (Tullio @fastmath emits qualified ops in Expr(:comparison))
    # `@fastmath`-style macros (e.g. Tullio's einsum kernel) build an
    # `Expr(:comparison, ...)` whose operators are *qualified* function
    # references such as `Base.FastMath.eq_fast` — a `K"."` field-access node,
    # not writable as infix source.  Comparison-chain desugaring must not
    # mistake that for a broadcast-dot operator (also `K"."`, but single-child)
    # and pull out its first child (`Base.FastMath`, a Module) as the callee.
    op = :(Base.FastMath.eq_fast)
    defn(head, ex) = Expr(:function, head, ex)
    chain3 = defn(:(c3(a,b,c)), Expr(:comparison, :a, op, :b, op, :c))
    single = defn(:(c1(a,b)),   Expr(:comparison, :a, op, :b))
    qual2  = defn(:(q2(a,b,c)), Expr(:comparison, :a, :(Base.:<), :b, :(Base.:<), :c))

    for fdef in (chain3, single, qual2)
        f = jl_eval(test_mod, fdef; expr_compat_mode=true)
        g = fl_eval(test_mod, fdef)
        for args in ((1,1,1), (1,1,3), (1,2,3), (3,2,1))
            n = length(fdef.args[1].args) - 1  # arity (drop the fn name)
            a = args[1:n]
            @test Base.invokelatest(f, a...) === Base.invokelatest(g, a...)
        end
    end
    # The exact observed shape: the chain drives an `if`.
    ifdef = defn(:(cif(a,b,c)),
                 Expr(:if, Expr(:comparison, :a, op, :b, op, :c), 1, 2))
    f = jl_eval(test_mod, ifdef; expr_compat_mode=true)
    @test Base.invokelatest(f, 1, 1, 1) === 1
    @test Base.invokelatest(f, 1, 1, 3) === 2
end

@testset "`.=` iteration spec (`@.` over a comprehension)" begin
    # From PkgEval: ApproximateVanishingIdeals v0.1.2, via FrankWolfe src/alternating_methods.jl:320 (@. y = [f(i) for i in ...])
    # `Base.__dot__` (the `@.` macro) guards `:for` but not `:generator`, so it
    # rewrites a comprehension's `i = 1:n` iteration spec into `i .= 1:n`.  flisp
    # binds an iterspec positionally and never inspects its head, so it accepts
    # the `.=` as an ordinary binding; the compat layer must match that leniency
    # or any use of `@.` around a comprehension/generator RHS fails to lower.
    gen(body, iters...) = Expr(:comprehension, Expr(:generator, body, iters...))
    dot(l, r) = Expr(:.=, l, r)
    forloop(iter, body) = Expr(:for, iter, body)
    cases = Any[
        gen(:(2i), dot(:i, :(1:3))),                                  # single
        gen(:(10i + j), dot(:i, :(1:2)), dot(:j, :(1:3))),            # cartesian
        gen(:i, Expr(:filter, :(isodd(i)), dot(:i, :(1:5)))),        # filter
        gen(:(a + b), dot(Expr(:tuple, :a, :b), :(zip(1:2, 10:11)))), # destructure
        Expr(:comprehension, Expr(:flatten,                          # nested/flatten
            Expr(:generator, Expr(:generator, :(10i + j), dot(:j, :(1:2))),
                 dot(:i, :(1:2))))),
        Expr(:typed_comprehension, :Float64,                         # typed
            Expr(:generator, :(2i), dot(:i, :(1:3)))),
        # plain for-loops: only reachable via an Expr (the parser rejects a `.=`
        # iterspec in surface syntax), but flisp lowers them, so we must too.
        Expr(:let, Expr(:(=), :s, 0),
             Expr(:block, forloop(dot(:i, :(1:4)), :(s += i)), :s)),  # single
        Expr(:let, Expr(:(=), :s, 0),                                 # block/multi
             Expr(:block,
                  forloop(Expr(:block, dot(:i, :(1:2)), dot(:j, :(1:3))),
                          :(s += 10i + j)), :s)),
        Expr(:let, Expr(:(=), :i, 0),                                 # `outer`
             Expr(:block, forloop(dot(Expr(:outer, :i), :(1:3)), :(nothing)), :i)),
    ]
    for ex in cases
        @test jl_eval(test_mod, ex; expr_compat_mode=true) == fl_eval(test_mod, ex)
    end

    # The real-world trigger: FrankWolfe's `grad!` (`@.` around a comprehension).
    src = """
        let storage = zeros(3), x = [1.0, 2.0, 3.0], N = 3
            @. storage = [2 * (x[i] - x[mod(i - 2, N) + 1]) for i in 1:N]
            storage
        end
        """
    @test jl_eval(test_mod, Meta.parse(src); expr_compat_mode=true) == [-4.0, 2.0, 2.0]

    # A `.=` iterspec is only leniency for `.=`: JuliaLowering stays strict on
    # genuinely nonsensical heads such as `+=` (which flisp accepts solely by
    # never checking the head, and which no macro emits).
    @test_throws JuliaLowering.LoweringError jl_eval(test_mod,
        gen(:(2i), Expr(:+=, :i, :(1:3))); expr_compat_mode=true)
end
