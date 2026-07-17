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

    @testset "(AI) escaped trailing LineNumberNode absorbed like a bare one" begin
        # OhMyThreads' `@tasks` esc-wraps every for-body statement -- including the
        # trailing parser LineNumberNode -- leaving `Expr(:escape, LineNumberNode)`
        # in tail position of the generated function body. flisp strips the
        # `escape` during hygiene (src/macroexpand.scm) and then treats the bare
        # line node as transparent metadata, so JuliaLowering must absorb it here
        # at `Expr` ingestion rather than leave a value-producing
        # `K"Value"(LineNumberNode)` behind (which the block would then *return*).
        LNN = LineNumberNode(999, :probe)

        # A single esc / hygienic-scope wrapper around a linenode is absorbed into
        # provenance (dropped as a statement), exactly like a bare block child.
        for wrap in (x->Expr(:escape, x),
                     x->Expr(Symbol("hygienic-scope"), x, @__MODULE__))
            st = JuliaLowering.expr_to_est(Expr(:block, :a, wrap(LNN)))
            @test kind(st) === K"block"
            @test numchildren(st) == 1
            @test kind(st[1]) === K"Identifier" && st[1].name_val == "a"
        end
        # ... including in leading position (block is not the `(a; b)` shape).
        st = JuliaLowering.expr_to_est(Expr(:block, Expr(:escape, LNN), :a))
        @test numchildren(st) == 1 && st[1].name_val == "a"

        # NON-linenode escaped payloads stay values and must NOT be absorbed:
        #   esc(99)                   -> a real value
        #   esc(QuoteNode(LNN))       -> a real (quoted) value
        #   esc(Expr(:meta, :inline)) -> a meta statement (flisp's `only-meta?`
        #                                does not skip `meta`, so it is kept)
        for payload in (99, QuoteNode(LNN), Expr(:meta, :inline))
            st = JuliaLowering.expr_to_est(Expr(:block, :a, Expr(:escape, payload)))
            @test numchildren(st) == 2
            @test kind(st[2]) === K"escape"
        end

        # Only ONE wrapper layer is peeled, matching flisp's single hygiene pop:
        # a doubly-escaped linenode is an over-escape (rejected by both lowerers),
        # so the inner escape must survive as a node for macro expansion to reject.
        st = JuliaLowering.expr_to_est(Expr(:block, :a, Expr(:escape, Expr(:escape, LNN))))
        @test numchildren(st) == 2
        @test kind(st[2]) === K"escape" && kind(st[2][1]) === K"escape"
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

    @testset "quoted Expr value preserves LineNumberNode absence" begin
        # A quoted block that is a VALUE (e.g. a macro return) is inert data:
        # its args -- including the *absence* of LineNumberNodes left by
        # `Base.remove_linenums!`, an extremely common canonicalization idiom --
        # must round-trip verbatim, matching flisp's inert quote payloads.
        # Consumers compare such rebuilt Exprs with `==`/`hash` (ForwardMethods.jl
        # via TestingUtilities `@test_cases`); re-synthesizing macrocall-site
        # linenodes into the payload breaks that.
        stripped = Expr(:block, :(z = f()), :(g(z)))       # no LineNumberNodes
        @test roundtrip(Expr(:quote, stripped)) == Expr(:quote, stripped)
        @test roundtrip(QuoteNode(stripped)) == QuoteNode(stripped)
        # Existing linenodes inside a quoted block are still preserved exactly
        # (only their absence was being lost):
        with_lnn = Expr(:block, LineNumberNode(99, :foo), :(p()), :(q()))
        @test roundtrip(QuoteNode(with_lnn)) == QuoteNode(with_lnn)
        # An empty quoted block stays empty (no synthesized provenance linenode)
        # and nested quote-in-quote keeps the inner payload verbatim:
        @test roundtrip(QuoteNode(Expr(:block))) == QuoteNode(Expr(:block))
        @test roundtrip(Expr(:quote, Expr(:quote, stripped))) ==
            Expr(:quote, Expr(:quote, stripped))

        # End-to-end through the macro pipeline (the ForwardMethods failure
        # shape): a macro that strips linenodes and returns a quoted block must
        # yield exactly that 2-statement block at runtime, with no linenodes.
        val = JuliaLowering.include_string(test_mod, """
            macro q_strip()
                ex = :(begin z = f(); g(z) end)
                Base.remove_linenums!(ex)
                Expr(:quote, ex)
            end
            @q_strip
            """; expr_compat_mode=true)
        @test val == Expr(:block, :(z = f()), :(g(z)))
        @test count(a -> a isa LineNumberNode, val.args) == 0
    end

    @testset "block leading-linenode shape (flisp parity)" begin
        # flisp/JuliaSyntax emit a linenode before every block child EXCEPT the
        # leading one of a parenthesized `(a; b)` compound (and `(;;)` stays
        # empty), regardless of line structure. Third-party macros hard-code
        # these element counts when matching `do (acc = init; x)`-style
        # arguments (FLoops.jl `analyze_rf_args` accepts only `block,2` or
        # `block,3` with an interior linenode), so a leading linenode is
        # shape-breaking for macro arguments.
        blockshape(ex) = (length(ex.args),
                          !isempty(ex.args) && ex.args[1] isa LineNumberNode)
        est(str) = JL.est_to_expr(JS.parsestmt(SyntaxTree, str))
        @test blockshape(est("(a = 0; b)")) == (3, false)
        @test blockshape(est("(a = 0;\nb)")) == (3, false)   # parens rule, not line-based
        @test blockshape(est("(a = 0; b; c)")) == (5, false)
        @test blockshape(est("begin a; b end")) == (4, true) # begin keeps leading
        @test blockshape(est("begin\na\nb\nend")) == (4, true)
        @test blockshape(est("(;;)")) == (0, false)
        @test blockshape(est("begin end")) == (1, true)

        # Round-trip: a block Expr without a leading linenode must not grow one
        # (nested macro expansion re-materializes spliced macro arguments).
        rt1 = roundtrip(Expr(:block, :(a = 0), :b))
        @test !(rt1.args[1] isa LineNumberNode)
        @test roundtrip(Expr(:block)) == Expr(:block)
        # A begin-style layout (leading linenode) keeps it verbatim.
        beginish = Expr(:block, LineNumberNode(7, :x), :(a = 0), LineNumberNode(8, :x), :b)
        @test roundtrip(beginish) == beginish

        # End-to-end: the FLoops.jl `@reduce() do (acc = 0; x)` shape -- the
        # do-argument tuple's block must arrive as `block,3` with the only
        # linenode in the middle.
        shp = JuliaLowering.include_string(test_mod, """
            macro rfshape(ex)
                blk = ex.args[1].args[1]   # do-lambda -> arg tuple -> block
                QuoteNode((length(blk.args),
                           findall(a -> a isa LineNumberNode, blk.args)))
            end
            @rfshape() do (acc = 0; x)
                acc + x
            end
            """; expr_compat_mode=true)
        @test shp == (3, [2])
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

@testset "flisp `(lambda ... (scope-block ...))` idiom (Tricks.jl/ValSplit)" begin
    # Tricks.jl's `create_codeinfo_with_returnvalue` (used by ValSplit for
    # compile-time dispatch, e.g. via PDDL) hand-builds an already-lowered
    # `Expr(:lambda, argnames, Expr(:scope-block, body))` and feeds it back
    # through `Meta.lower`. flisp accepts this natively; JuliaLowering must too.
    # Two things previously diverged: the argnames slot is a `Vector{Symbol}`
    # (not `Vector{Any}`), and the flisp-internal `scope-block` body — a
    # lowering-only form — merely delimits the lambda's own scope.
    for (argnames, body) in [
            # `Vector{Symbol}` argnames — the exact type Tricks.jl constructs
            ([Symbol("#self#"), :x], Expr(:block, Expr(:return, 1))),
            # `Vector{Any}` argnames must keep working too
            (Any[Symbol("#self#"), :x], Expr(:block, Expr(:return, 1))),
            ([Symbol("#self#"), :x], Expr(:block, Expr(:return, :x))),
            # a body with a local binding exercises the lambda's (hard) scope
            ([Symbol("#self#"), :x],
                Expr(:block, Expr(:(=), :y, 5), Expr(:return, :y))),
        ]
        expr = Expr(:lambda, argnames, Expr(Symbol("scope-block"), body))
        out = JL.core_lowering_hook(expr, test_mod)
        @test out isa Core.SimpleVector && out[1] isa Core.CodeInfo
        # flisp parity: the default lowerer here is flisp, so compare directly.
        flisp_ci = Meta.lower(test_mod, expr)
        @test flisp_ci isa Core.CodeInfo
        @test out[1].code == flisp_ci.code
    end
end

@testset "flisp `with-static-parameters` lambda wrapper (Tricks.jl `spnames`)" begin
    # With non-nothing `spnames`, Tricks.jl's `create_codeinfo_with_returnvalue`
    # (via ValSplit -> PDDL, and MacroUtilities' `@method_def_constant` ->
    # ForwardMethods) additionally wraps the hand-built lambda in flisp's
    # sparam-binding form, `(with-static-parameters lam sp1 sp2 ...)`, which
    # binds the given names positionally as the lambda's static parameters.
    mklam(argnames, body) =
        Expr(:lambda, argnames, Expr(Symbol("scope-block"), body))
    for (spnames, body) in [
            ([:T], Expr(:block, Expr(:return, 1))),
            # PDDL's exact shape: several sparams, constant return value
            ([:T, :N, :P], Expr(:block, Expr(:return, 1))),
            (Symbol[], Expr(:block, Expr(:return, 1))),
            # a body referencing an sparam exercises the actual binding
            ([:T, :N, :P], Expr(:block, Expr(:return, :P))),
        ]
        expr = Expr(Symbol("with-static-parameters"),
                    mklam([Symbol("#self#"), :x], body), spnames...)
        out = JL.core_lowering_hook(expr, test_mod)
        @test out isa Core.SimpleVector && out[1] isa Core.CodeInfo
        flisp_ci = Meta.lower(test_mod, expr)
        @test flisp_ci isa Core.CodeInfo
        @test out[1].code == flisp_ci.code
    end
    # sparam references resolve to the *positional* index, matching flisp
    expr = Expr(Symbol("with-static-parameters"),
                mklam([Symbol("#self#"), :x], Expr(:block, Expr(:return, :P))),
                :T, :N, :P)
    ci = JL.core_lowering_hook(expr, test_mod)[1]
    @test any(==(Expr(:static_parameter, 3)), ci.code)
    # a non-lambda payload stays rejected (flisp: "malformed expression"). The
    # hook converts this non-internal lowering error to `ErrorException` for
    # flisp compat (see the `core_lowering_hook` path testset in test/hooks.jl).
    bad = Expr(Symbol("with-static-parameters"), Expr(:block, Expr(:return, 1)), :T)
    @test_throws ErrorException JL.core_lowering_hook(bad, test_mod)
end

@testset "`(meta generated gen)` keeps the generator evaluable" begin
    # Generated functions declared with the raw stub idiom reference their
    # generator BY NAME (MacroUtilities' `@method_def_constant`, e.g. in
    # ForwardMethods; also Base's bootstrap):
    #     function f(...); $(Expr(:meta, :generated, gen_name)); ...; end
    # The runtime resolves the payload by *evaluating* it at method-definition
    # time (`method.c`'s `jl_toplevel_eval`), so it must stay a real binding
    # reference. Blanket-quoting it like other meta payloads made the
    # "generator" the `Symbol` itself, and the first staged call then crashed
    # with "objects of type Symbol are not callable".
    Core.eval(test_mod, quote
        function _mdc_gen(world, source, self)
            ex = Expr(:lambda, [Symbol("#self#")],
                      Expr(Symbol("scope-block"), Expr(:block, Expr(:return, 42))))
            ci = Meta.lower(@__MODULE__, ex)
            ci.edges = Core.svec()
            ci.min_world = one(UInt64)
            ci.max_world = typemax(UInt64)
            return ci
        end
    end)
    fdef = Expr(:function, Expr(:call, :_mdc_f),
        Expr(:block,
            Expr(:meta, :generated, :_mdc_gen),
            Expr(:meta, :generated_only)))
    out = JL.core_lowering_hook(fdef, test_mod)
    @test out isa Core.SimpleVector
    Core.eval(test_mod, out[1])
    f = Base.invokelatest(getglobal, test_mod, :_mdc_f)
    @test first(methods(f)).generator isa Function
    @test Base.invokelatest(f) == 42
end


@testset "qualified operator in comparison chain (Tullio `@fastmath` rewrite)" begin
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

# Found via RomanNumerals v0.3.3 in a PkgEval comparison against flisp lowering.
#
# `x ^ n` is rewritten to `Base.literal_pow(^, x, Val(n))` only when `n` is a
# literal integer.  flisp's `julia-syntax.scm` gates this on the scheme-level
# `integer?` predicate, which (via `julia_to_scm`/`jl_is_long` in `src/ast.c`)
# is true for exactly a native Julia `Int` and nothing else.  A macro that
# returns a *value* embeds it as a literal in the AST, so any `Integer`-subtyped
# value (`Int8`, `UInt64`, `Int128`, `BigInt`, `Bool`, or a user struct such as
# RomanNumerals' `RomanNumeral <: Integer`) can appear as the exponent.  The
# compat layer previously tested `isa Integer`, which matched all of these and
# wrongly bypassed the value's own `^` method (and for `Val`-illegal values such
# as `BigInt`/`RomanNumeral`, threw a `TypeError` in `Core.apply_type`).  The
# predicate must instead be `isa Int`, matching flisp's accept set exactly.
module LitPowProbe
    # `P` observes which `^` path lowering picked.
    struct P end
    Base.:^(::P, n) = (:direct, n)
    Base.literal_pow(::typeof(^), ::P, ::Val{n}) where {n} = (:litpow, n)
    # `RN` mirrors RomanNumerals' `RomanNumeral <: Integer` with a value-returning
    # string macro; `rn"..." ^ rn"..."` must dispatch to the vararg `^` below.
    struct RN <: Integer
        val::Int
    end
    Base.:^(a::RN, b::RN...) = RN(99)
    Base.:(==)(a::RN, b::RN) = a.val == b.val
    macro rn_str(s); RN(parse(Int, s)); end
end

@testset "(AI) literal_pow rewrite matches flisp's `integer?` (Int only)" begin
    P = LitPowProbe.P
    mkpow(v) = Expr(:call, :^, P(), v)

    # (shape => whether flisp/JL should take the literal_pow path).  The exponent
    # is embedded as a literal *value* of each Integer subtype, exactly as a
    # value-returning macro would produce it.  Only a native `Int` is rewritten.
    battery = [
        (Int64(2),              true),
        (Int32(2),              false),
        (Int16(2),              false),
        (Int8(2),               false),
        (UInt64(2),             false),
        (UInt32(2),             false),
        (UInt16(2),             false),
        (UInt8(2),              false),
        (Int128(2),             false),
        (UInt128(2),            false),
        (BigInt(2),             false),
        (true,                  false),   # Bool <: Integer, but flisp says no
        (false,                 false),
    ]
    for (v, is_litpow) in battery
        ex = mkpow(v)
        expected = is_litpow ? (:litpow, v) : (:direct, v)
        # Direct assertion of the chosen path...
        @test jl_eval(test_mod, ex) == expected
        # ...and parity with flisp as the oracle.
        @test jl_eval(test_mod, ex) == fl_eval(test_mod, ex)
    end

    # Source-level integer literals (including a negative literal) are native
    # `Int`s and are rewritten in both lowerers.
    Core.eval(test_mod, :(pp = $(P())))
    for src in ("pp ^ 2", "pp ^ -2", "pp ^ 0")
        ex = Meta.parse(src)
        @test jl_eval(test_mod, ex) == fl_eval(test_mod, ex)
        @test first(jl_eval(test_mod, ex)) === :litpow
    end

    # A `Float64` exponent is never rewritten (regression guard on the shape
    # neighbouring the fix).
    let ex = mkpow(2.0)
        @test jl_eval(test_mod, ex) == (:direct, 2.0) == fl_eval(test_mod, ex)
    end

    # The original RomanNumerals reproduction.  `@rn_str` returns a
    # `RomanNumeral <: Integer` *value*, so macro expansion embeds it directly as
    # a literal exponent -- reproduced here by embedding `RN` values into the AST
    # (the macro is not required for the defect).  With the fix this reaches the
    # package's own vararg `^` in both lowerers; before it, JL applied `Val` to a
    # non-`Int` and threw `TypeError`.
    RN = LitPowProbe.RN
    rn_expr = Expr(:call, :(==), Expr(:call, :^, RN(20), RN(2)), RN(99))
    @test jl_eval(test_mod, rn_expr) === true
    @test fl_eval(test_mod, rn_expr) === true
end
