using JuliaLowering: compress_sbt, uncompress_sbt, SourceByteTable,
    add_debuginfo!

test_mod = Module()

function test_byte_precise(di::Core.DebugInfo, nstmts::Int)
    for i in 1:nstmts
        sl = Base.Compiler.source_location(di, i)
        @test sl.byte > 0      context=di
        @test sl.byte_end > 0  context=di
        @test sl.col > 0       context=di
        @test sl.col_end > 0   context=di
        @test sl.line > 0      context=di
        @test sl.line_end > 0  context=di
    end
end

@testset "SourceByteTable roundtrip" begin
    st = jl_lower(test_mod, JuliaSyntax.parsestmt(SyntaxTree, "1 + 2 - \n 3"))
    JuliaSyntax.ensure_attributes!(st._graph; debuginfo=Any)
    add_debuginfo!(st)
    csbt = st.debuginfo
    usbt = uncompress_sbt(csbt)
    cusbt = compress_sbt(usbt)
    @test csbt isa Core.DebugInfo
    @test usbt isa SourceByteTable
    @test cusbt isa String
    @test cusbt === csbt.linetable

    @test length(usbt.spans) <= numchildren(st[1]) # lhs is unique locs
    test_byte_precise(csbt, numchildren(st[1]))
end

@testset "Attaching DebugInfo to methods" begin
    local f = JuliaLowering.include_string(test_mod, """
    function f_with_debuginfo(x)
        show(x)
        map(a->a+1, x)
    end
    """)
    di = methods(f)[1].debuginfo
    @test di.linetable isa String
    let nstmts = length(Base._uncompressed_ir(methods(f)[1]).code)
        test_byte_precise(di, nstmts)
    end
end

@testset "Stack traces can read our debuginfo" begin
    f_errors = JuliaLowering.eval(
        test_mod,
        Expr(:function, Expr(:call, :func_throws_at_myfile_200),
             Expr(:block,
                  LineNumberNode(100, :myfile),
                  LineNumberNode(200, :myfile),
                  Expr(:call, :error, "foo"),
                  LineNumberNode(300, :myfile),
                  :(return y * 2))))
    frames = try
        f_errors()
        @test false=="expected error"
    catch err
        stacktrace(catch_backtrace())
    end
    myframe_i = findfirst(x->x.func==:func_throws_at_myfile_200, frames)
    @test myframe_i == 2
    # TODO: line field may disappear
    @test frames[myframe_i].line == 200
end

@testset "backtrace line matches own provenance in macro-generated code" begin
    # The innermost backtrace frame of an exception thrown from macro-generated
    # code must report the throwing statement's *own* (nearest embedded line
    # node) location, matching flisp — not the outermost enclosing macrocall.
    # (Exception: the deeply-nested cell below, a documented flisp divergence.)
    # See `_di_srcref`/`_di_pos` in eval.jl. The expected line is the
    # 1-based line of the throwing statement within `usage`.
    #
    # `defs` are evaluated normally (compiled functions, as a package's macros
    # would be); `usage` is lowered byte-precisely by `JuliaLowering.include_string`
    # and stores the caught backtrace line into the module global `gl`.
    function caught_line(defs, usage)
        m = Module(:BtMod)
        Core.eval(m, :(using Base))
        for d in defs
            Core.eval(m, d)
        end
        JuliaLowering.include_string(m, usage, "usage.jl")
        return Core.eval(m, :gl)::Int
    end

    wrap    = :(macro wrap(body);  quote; $body; end; end)
    escwrap = :(macro wrap(body);  quote; $(esc(body)); end; end)
    boom    = :(macro boom(); Expr(:block, __source__, :(throw(ErrorException("boom")))); end)
    w1 = :(macro wrap1(body); quote; $body; end; end)
    w2 = :(macro wrap2(body); quote; $body; end; end)
    w3 = :(macro wrap3(body); quote; $body; end; end)
    catcher = "catch e\n    global gl = stacktrace(catch_backtrace())[1].line\nend\n"

    # V1: throw via inner `@boom` (`__source__`) nested inside `@wrap`'s body
    @test caught_line([boom, wrap], "gl = 0\n@wrap try\n    @boom()\n$catcher") == 3
    # V2: plain `throw` inside `@wrap`'s body (no inner macro)
    @test caught_line([wrap], "gl = 0\n@wrap try\n    throw(ErrorException(\"x\"))\n$catcher") == 3
    # V3: multi-statement `@wrap` body, throw on a later line
    @test caught_line([wrap], "gl = 0\n@wrap try\n    a = 1\n    b = 2\n    throw(ErrorException(\"x\"))\n$catcher") == 5
    # Deeply nested: three wrapping macros around an inner `@boom`.
    # NOTE deliberate flisp divergence: because the wrap macros are defined
    # outside the `usage` "file", flisp emits a multi-frame "macro expansion"
    # chain here whose innermost frame points into the macro-*definition*
    # context (its line is a harness-dependent artifact), and whose usage-file
    # chain entry is line 3.  JL's single-file debuginfo cannot emit that
    # chain; it reports one frame at the nearest usage-file provenance —
    # line 3, agreeing with flisp's usage-file entry (and with flisp's
    # innermost frame when the macros are defined in the *same* file).
    @test caught_line([boom, w1, w2, w3], "gl = 0\n@wrap1 @wrap2 @wrap3 try\n    @boom()\n$catcher") == 3
    # esc'd body: escaping the interpolated body does not change line attribution
    @test caught_line([escwrap], "gl = 0\n@wrap try\n    throw(ErrorException(\"x\"))\n$catcher") == 3
    # Control: a plain (non-macro) function reports its own throw line, unchanged
    @test caught_line([], "gl = 0\nf() = throw(ErrorException(\"x\"))\ntry\n    f()\n$catcher") == 2
end

@testset "spliced Expr keeps its own embedded line provenance" begin
    # A code `Expr` carrying its own embedded `LineNumberNode`s (a `quote`
    # literal built elsewhere, e.g. a test stored in a `Dict`) spliced via `$f`
    # into an `@eval` wrapper must report *its own* line in a thrown exception's
    # backtrace, not the interpolation site's line.  This is
    # ParallelTestRunner.jl's shape (a `quote`-literal test spliced into an
    # `@eval mod begin ... $f ... end` runner); flisp preserves the spliced
    # `Expr`'s own provenance, so `interpolate_syntax` must honor its linenodes
    # rather than stamping them with the `$f` site (see `_interpolate_syntax`).
    m = Module(:SpliceLineMod)
    Core.eval(m, :(using Base))
    # `f` (line 3) is the throwing statement's own line; the `$ff` splice site
    # is line 7.  The reported line must be 3, not 7.
    usage = join([
        "gl = 0",                                                   # 1
        "f = quote",                                                # 2
        "    throw(ErrorException(\"x\"))",                         # 3  <- f's own line
        "end",                                                      # 4
        "function ex(mod, ff)",                                     # 5
        "    @eval mod begin",                                      # 6
        "        \$ff",                                             # 7  <- interpolation site
        "    end",                                                  # 8
        "end",                                                      # 9
        "try",                                                      # 10
        "    ex(@__MODULE__, f)",                                   # 11
        "catch e",                                                  # 12
        "    global gl = stacktrace(catch_backtrace())[1].line",   # 13
        "end",                                                      # 14
    ], "\n") * "\n"
    JuliaLowering.include_string(m, usage, "usage.jl")
    @test Core.eval(m, :gl) == 3
end

@testset "macro-expansion frames match flisp's line shape" begin
    # flisp holds the root codeloc of every statement inside a macro expansion
    # at the region's first in-file line (`push_loc` regions never advance the
    # root-level current line); the statement's own line lives in the deepest
    # "macro expansion" edge. Check both on a `@testset`/`@test` body, the
    # shape Test's backtrace-scrubbing suite asserts on.
    m = Module(:MacroFrameMod)
    Core.eval(m, :(using Base, Test))
    src = "@testset \"t\" begin\n    @test 1 == 2\nend"
    st = jl_lower(m, JuliaSyntax.parsestmt(SyntaxTree, src; filename="usage.jl"))
    JuliaSyntax.ensure_attributes!(st._graph; debuginfo=Any)
    add_debuginfo!(st)
    di = st.debuginfo
    testfile = basename(String(first(methods(Test.do_test)).file))
    deepest = Set{Tuple{String,Int}}()
    for pc in 1:numchildren(st[1])
        loc = ccall(:jl_uncompress1_codeloc, NTuple{3,Int32}, (Any, Int), di, pc)
        to, epc = Int(loc[2]), Int(loc[3])
        to == 0 && continue
        # Every edge-carrying statement's root line is the region anchor:
        # the `@testset` body's first in-file line.
        @test Base.Compiler.source_location(di, pc).line == 2
        d = di
        file = ""; line = 0
        while to != 0
            e = d.edges[to]::Core.DebugInfo
            eloc = ccall(:jl_uncompress1_codeloc, NTuple{3,Int32}, (Any, Int), e, epc)
            file = basename(String(e.def::Symbol)); line = Int(eloc[1])
            d = e; to = Int(eloc[2]); epc = Int(eloc[3])
        end
        push!(deepest, (file, line))
    end
    # The `@test` statements' own location, one macro-expansion frame per file
    # boundary: a Test.jl frame (the machinery) and the usage-file frame at
    # the `@test` line.
    @test ("usage.jl", 2) in deepest
    @test any(f -> f[1] == testfile, deepest)
end

@testset "eval'd thunk adopts the quoted arguments' source file" begin
    # flisp locates a thunk with no real source context (`eval` of a
    # hand-built `Expr(:macrocall, name, nothing, ...)`) at the first
    # real-file line node inside the code -- the caller's quoted arguments.
    m = Module(:AltSrcMod)
    Core.eval(m, :(using Base))
    Core.eval(m, :(macro identwrap(x); esc(x); end))
    q = quote
        1 + 1
    end # the quote's LineNumberNodes point at *this* file
    qline = q.args[1].line
    ex = Expr(:macrocall, Symbol("@identwrap"), nothing, q)
    st = jl_lower(m, JuliaLowering.expr_to_est(ex, LineNumberNode(1, :none));
                  expr_compat_mode=true)
    JuliaSyntax.ensure_attributes!(st._graph; debuginfo=Any)
    add_debuginfo!(st)
    di = st.debuginfo
    @test di.def === Symbol(@__FILE__)
    @test Base.Compiler.source_location(di, 1).line == qline
end

@testset "cross-file macro content keeps byte-precise debuginfo" begin
    # Statements whose own provenance names a *foreign* file (a macro body
    # defined in another file/context) are attributed to their macrocall site
    # in the lowered file: silently (no "inconsistent provenance" warnings)
    # and without degrading the CodeInfo to line-based debuginfo.
    m = Module(:XFMod)
    Core.eval(m, :(using Base))
    # The quoted macro body's line nodes point at *this* file, foreign to the
    # "usage.jl" text lowered below.
    Core.eval(m, :(macro deffn()
        esc(quote
            function genfn_xf(x)
                x + 1
            end
        end)
    end))
    f = @test_logs JuliaLowering.include_string(m, "@deffn()\ngenfn_xf", "usage.jl")
    @test f(1) == 2
    if JuliaLowering._has_byte_precise_debuginfo
        @test methods(f)[1].debuginfo.linetable isa String
    end
end

@testset "synthetic-context thunk emits foreign-file macro-expansion frames" begin
    # A thunk with no real source context (`Core.eval` of a hand-built `Expr`,
    # file "none") that wraps *foreign-file* content in a macrocall must still
    # emit a "macro expansion" edge at the foreign line, matching flisp's
    # `push_loc`.  This is ParallelTestRunner.jl's shape: an old-syntax `@eval`
    # lowers to `Core.eval` of an `Expr` built by `interpolate_expr`, splicing a
    # test `quote` from another file into a `@testset` wrapper.  The thunk
    # adopts the wrapper's file as its root (`_thunk_alt_source`); the spliced
    # code's own file is one level inside it and had been dropped because the
    # macro-edge grouping keyed on the synthetic `:none` name instead of the
    # adopted file (see `add_debuginfo!`/`_macro_edge_groups`).
    m = Module(:XFThunkMod)
    Core.eval(m, :(using Base))
    Core.eval(m, :(macro identwrap(x); esc(x); end))
    ex = Expr(:block,
        LineNumberNode(17, Symbol("outer.jl")),
        Expr(:macrocall, Symbol("@identwrap"), LineNumberNode(17, Symbol("outer.jl")),
            Expr(:block,
                LineNumberNode(4, Symbol("inner.jl")),
                :(error("x")))))
    st = jl_lower(m, JuliaLowering.expr_to_est(ex, LineNumberNode(1, :none));
                  expr_compat_mode=true)
    JuliaSyntax.ensure_attributes!(st._graph; debuginfo=Any)
    add_debuginfo!(st)
    di = st.debuginfo
    # The thunk adopts the wrapper file (`outer.jl`) as its root.
    @test di.def === Symbol("outer.jl")
    # Walk each statement's edge chain to its deepest "macro expansion" frame.
    deepest = Set{Tuple{String,Int}}()
    for pc in 1:numchildren(st[1])
        loc = ccall(:jl_uncompress1_codeloc, NTuple{3,Int32}, (Any, Int), di, pc)
        to, epc = Int(loc[2]), Int(loc[3])
        to == 0 && continue
        # Root codeloc stays at the adopted-file region anchor.
        @test Base.Compiler.source_location(di, pc).line == 17
        d = di; file = ""; line = 0
        while to != 0
            e = d.edges[to]::Core.DebugInfo
            eloc = ccall(:jl_uncompress1_codeloc, NTuple{3,Int32}, (Any, Int), e, epc)
            file = basename(String(e.def::Symbol)); line = Int(eloc[1])
            d = e; to = Int(eloc[2]); epc = Int(eloc[3])
        end
        push!(deepest, (file, line))
    end
    # The spliced `error(...)`'s own foreign line is emitted as a frame.
    @test ("inner.jl", 4) in deepest
end

@testset "(AI) transparent-macrocall round-trip emits no spurious edge" begin
    # Found via SimpleTraits v0.9.6 in a PkgEval comparison against flisp
    # lowering. A macro (SimpleTraits' `@traitfn`) co-emits, through a *shallow*
    # `MacroTools.rmlines`, a nested `quote` redirect plus the user's method
    # wrapped in a transparent macrocall (`Base.@__doc__`). The shallow rmlines
    # strips the outer block's line nodes but leaves the nested quote's, whose
    # foreign line then gets inherited by the adjacent `@__doc__` macrocall. The
    # user method's body (its own text in the usage file) therefore acquires a
    # macro-provenance chain that leaves the usage file, touches that foreign
    # line, and returns to the *same* usage line -- a transparent round-trip the
    # content never really crossed. flisp reports the body flat at its own line;
    # JuliaLowering used to emit a bogus `usage -> foreign -> usage` macro-
    # expansion edge, so the innermost backtrace frame was named `"macro
    # expansion"` instead of the method, and rendered a fabricated
    # (foreign-file, usage-line) pair. See `_macro_edge_groups` in eval.jl.
    m = Module(:RoundTripMod)
    Core.eval(m, :(using Base))
    # A transparent macro (re-emits its argument), like `Base.@__doc__`.
    Core.eval(m, :(macro passthrough(x); esc(x); end))
    # rmlines that only strips the *direct* block children (like MacroTools').
    Core.eval(m, :(_rmshallow(ex::Expr) =
        Expr(ex.head, filter(a -> !(a isa LineNumberNode), ex.args)...)))
    Core.eval(m, :(_rmshallow(x) = x))
    # A generator macro whose expansion is a shallow-rmlined block of a nested
    # `quote` (its line node in *this* file, foreign to usage.jl) followed by
    # `@passthrough <userdef>`.
    Core.eval(m, :(macro gen(fdef)
        dispatch = quote
            _gen_redirect_dummy() = nothing
        end
        esc(_rmshallow(quote
            $dispatch
            @passthrough $fdef
        end))
    end))
    usage = join([
        "gl = 0",                                                  # 1
        "@gen gfn() = throw(ErrorException(\"x\"))",               # 2  <- gfn body
        "try",                                                     # 3
        "    gfn()",                                               # 4
        "catch e",                                                 # 5
        "    global gl = stacktrace(catch_backtrace())",           # 6
        "end",                                                     # 7
    ], "\n") * "\n"
    JuliaLowering.include_string(m, usage, "usage.jl")

    # The generated method's DebugInfo is flat: the round-trip through the
    # foreign file emits no "macro expansion" edge.
    gfn = Core.eval(m, :gfn)
    di = only(methods(gfn)).debuginfo
    @test di.def === Symbol("usage.jl")
    nstmts = length(Base._uncompressed_ir(only(methods(gfn))).code)
    for pc in 1:nstmts
        loc = ccall(:jl_uncompress1_codeloc, NTuple{3,Int32}, (Any, Int), di, pc)
        @test loc[2] == 0  # no edge index
    end

    # The innermost backtrace frame names the method (not "macro expansion")
    # and reports its own usage-file location -- no fabricated foreign pair.
    frames = Core.eval(m, :gl)::Vector{<:Base.StackTraces.StackFrame}
    l1 = frames[1]
    @test l1.func === :gfn
    @test occursin("usage.jl", string(l1.file))
    @test l1.line == 2
end
