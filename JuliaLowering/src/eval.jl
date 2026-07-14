# Non-incremental lowering API for non-toplevel non-module expressions.
# May be removed?

function lower(mod::Module, ex_in::SyntaxTree; expr_compat_mode::Bool=false,
               soft_scope::Union{Nothing,Bool}=nothing)
    ver = expr_compat_mode ? JL_OLD_SYNTAX_VERSION : JL_NEW_SYNTAX_VERSION
    ex0 = rebase_layers(ex_in, mod, ver)
    world = Base.get_world_counter()
    ex1 = expand_forms_1(ex0, world, true)
    ctx2, ex2 = expand_forms_2(ex1, world)
    ctx3, ex3 = resolve_scopes(ctx2, ex2; soft_scope)
    ctx4, ex4 = convert_closures(ctx3, ex3)
    _ctx5, ex5 = linearize_ir(ctx4, ex4)
    ex5
end

function macroexpand(mod::Module, ex_in::SyntaxTree;
                     expr_compat_mode::Bool=false,
                     ver::VersionNumber=expr_compat_mode ?
                         JL_OLD_SYNTAX_VERSION : JL_NEW_SYNTAX_VERSION,
                     recursive::Bool=true)
    ex0 = rebase_layers(ex_in, mod, ver)
    expand_forms_1(ex0, Base.get_world_counter(), recursive)
end

"May be used in macros or from any module"
function macroexpand(st::SyntaxTree)
    DEBUG && assert_expandable(st)
    ctx = MacroExpansionContext(st, Base.get_world_counter(), true)
    expand_forms_1(ctx, st)
end

# If a top-level thunk has existing context, we can assume all syntax has the
# same base layer: either it was produced by a macro expansion and went through
# `apply_expansion_layer`, or it was produced by parsing (which we assume either
# adds zero or uniform context to the tree).

# We ignore old the base layer's module, which should usually be the same as the
# current lowering module.  (counterexample: macroexpand in mod A producing
# escaped :toplevel st, then eval st in mod B, but flisp does the same thing by
# spamming globalrefs to mod A throughout st).
function rebase_layers(st, mod::Module, ver::VersionNumber,
                       remap_layer::Union{Nothing,ScopeLayer}=nothing)
    out = if !hasattr(st, :context)
        # assert zero context
        sc = SyntaxContext(mod, ver)
        fill_context!(st, sc)
    else
        # By default we remap the *base* layer (the module code was written in /
        # eval'd into) to `mod`. When walking into a `module` block whose body
        # carries macro-expansion hygiene (e.g. a `module` produced by an
        # unescaped macro quote and evaluated via `@eval`/`Core.eval`), the
        # unescaped body scope is the module's *outermost* layer rather than the
        # base layer, so `remap_layer` lets the caller target that layer instead.
        # This makes `using`/`import` and plain global references inside such a
        # module resolve against the freshly-created module, matching flisp.
        base = isnothing(remap_layer) ? base_layer(st.context::SyntaxContext) : remap_layer
        newbase = ScopeLayer(mod, nothing)
        _rebase_layers(
            st, Dict{ScopeLayer, ScopeLayer}(base=>newbase),
            Dict{SyntaxContext, SyntaxContext}())
    end
    DEBUG && assert_expandable(out)
    out
end

function _rebase_layers(st, slmap, scmap)
    sc = st.context::SyntaxContext
    sc2 = get(scmap, sc, nothing)
    if isnothing(sc2)
        sl2 = _get_sl!(slmap, sc.layer)
        sc2 = scmap[sc] = SyntaxContext(sl2, sc.unexpanded, sc.version, sc.internal)
    end
    if is_leaf(st) || numchildren(st) == 0
        setattr(st, :context, sc2)
    else
        setattr!(mapchildren(c->_rebase_layers(c, slmap, scmap), st._graph, st),
                 :context, sc2)
    end
end

function _get_sl!(slmap, sl::ScopeLayer)
    out = get(slmap, sl, nothing)
    out isa ScopeLayer && return out
    slmap[sl] = ScopeLayer(
        sl.mod, isnothing(sl.escaped) ? nothing : _get_sl!(slmap, sl.escaped))
end

# Incremental lowering API which can manage toplevel and module expressions.
#
# This iteration API is oddly bespoke and arguably somewhat non-Julian for two
# reasons:
#
# * Lowering knows when new modules are required, and may request them with
#   `:begin_module`. However `eval()` generates those modules so they need to
#   be passed back into lowering. So we can't just use `Base.iterate()`. (Put a
#   different way, we have a situation which is suited to coroutines but we
#   don't want to use full Julia `Task`s for this.)
# * We might want to implement this `eval()` in Julia's C runtime code or early
#   in bootstrap. Hence using SimpleVector and Symbol as the return values of
#   `lower_step()`
#
# We might consider changing at least the second of these choices, depending on
# how we end up putting this into Base.

# todo entries are (expr, is_module_body, child_idx, module_layer, reeval):
# * `module_layer`, when non-nothing, is the outermost hygiene layer of the
#   enclosing `module` block; its statements are rebased against that layer (see
#   `rebase_layers`) so that hygienic macro-generated module bodies resolve
#   against the freshly-created module.
# * `reeval` marks a subtree that is a *re-evaluated* hygienic payload — a
#   `module` handed to a fresh `eval()`/`Core.eval` (e.g. `@eval module ...`,
#   as `@safetestset` does). flisp re-evaluates such payloads through an inert
#   quote, which strips macro hygiene so every unescaped name binds/resolves in
#   the freshly-created module. We reproduce that by remapping the outermost
#   hygiene layer only for `reeval` modules and their nested modules. A `module`
#   produced *inline* by macro expansion (a macro that directly returns
#   `Expr(:toplevel, Expr(:module, ...))`, e.g. EnumX's `@enumx`) is not
#   re-evaluated: flisp keeps its hygiene, so unescaped references resolve back
#   to the macro's defining module. Such modules are reached as descendants
#   (`child_idx > 0`) with `reeval` unset and are left un-remapped.
struct LoweringIterator{Attrs}
    ver::VersionNumber # later stored in module?
    todo::Vector{Tuple{SyntaxTree{Attrs}, Bool, Int, Union{Nothing,ScopeLayer}, Bool}}
end

function lower_init(ex::SyntaxTree{T}, ver) where {T}
    LoweringIterator{T}(ver, [(ex, false, 0, nothing, false)])
end

function lower_step(iter::LoweringIterator, mod::Module, world::UInt;
                    soft_scope::Union{Nothing,Bool}=nothing)
    if isempty(iter.todo)
        return Core.svec(:done)
    end

    top_ex, is_module_body, child_idx, module_layer, reeval = pop!(iter.todo)
    root = child_idx == 0
    if child_idx > 0
        if child_idx <= numchildren(top_ex)
            push!(iter.todo, (top_ex, is_module_body, child_idx + 1, module_layer, reeval))
            ex = top_ex[child_idx]
        elseif is_module_body
            return Core.svec(:end_module)
        else
            return lower_step(iter, mod, world; soft_scope)
        end
    else
        ex = top_ex
    end

    k = kind(ex)
    if !(k in KSet"toplevel module")
        ex = rebase_layers(ex, mod, iter.ver, module_layer)
        ex = expand_forms_1(ex, world, true)
        k = kind(ex)
    end
    if k == K"toplevel"
        push!(iter.todo, (ex, false, 1, nothing, reeval))
        return lower_step(iter, mod, world; soft_scope)
    elseif k == K"module"
        (version, notbare, name, body) = @stm ex begin
            [K"module" version nb_st name body] ->
                (version.value, nb_st.value, name, body)
            [K"module" nb_st name body] ->
                (nothing, nb_st.value, name, body)
        end
        if kind(name) != K"Identifier"
            throw(LoweringError(name, "Expected module name"))
        end
        newmod_name = Symbol(name.name_val)
        loc = source_location(LineNumberNode, ex)
        # Remap the body's outermost hygiene layer into the new module only for
        # re-evaluated payloads: a `module` handed to a fresh `eval()` (reached
        # as the iterator root, `root`) or nested inside such a payload
        # (`reeval`). flisp strips hygiene from these (they pass through `@eval`'s
        # inert quote), so unescaped `using`/`import` targets and global names
        # bind/resolve in the freshly-created module. A `module` produced inline
        # by macro expansion (returned directly as `Expr(:module, ...)`) is not
        # re-evaluated: keeping its hygiene makes unescaped references resolve to
        # the macro's defining module, matching flisp. Parsed literal modules
        # carry no context and fall back to default (base-layer) rebasing.
        module_reeval = reeval || root
        body_layer = (module_reeval && hasattr(ex, :context)) ? ex.context.layer : nothing
        push!(iter.todo, (body, true, 1, body_layer, module_reeval))
        return Core.svec(:begin_module, version, newmod_name, notbare, loc)
    else
         ctx2, ex2 = expand_forms_2(ex, world)
         ctx3, ex3 = resolve_scopes(ctx2, ex2; soft_scope)
         ctx4, ex4 = convert_closures(ctx3, ex3)
        _ctx5, ex5 = linearize_ir(ctx4, ex4)
        thunk = to_lowered_expr(ex5)
        return Core.svec(:thunk, thunk)
    end
end


#-------------------------------------------------------------------------------

function codeinfo_has_image_globalref(@nospecialize(e))
    if e isa GlobalRef
        return 0x00 !== @ccall jl_object_in_image(e.mod::Any)::UInt8
    elseif e isa Core.CodeInfo
        return any(codeinfo_has_image_globalref, e.code)
    else
        return false
    end
end

function codeinfo_has_fcall(@nospecialize(e))
    if e isa Expr
        if e.head === :(=)
            return codeinfo_has_fcall(e.args[2])
        end
        return e.head === :foreigncall || e.head === :foreignglobal ||
            e.head === :cfunction
    end
    return false
end

const _CodeInfo_need_ver = v"1.12.0-DEV.512"
@static if VERSION < _CodeInfo_need_ver
    function _CodeInfo(args...)
        error("Constructing a CodeInfo using JuliaLowering currently requires Julia version $_CodeInfo_need_ver or greater")
    end
else
    # debuginfo changed completely as of https://github.com/JuliaLang/julia/pull/52415
    # nargs / isva was added as of       https://github.com/JuliaLang/julia/pull/54341
    # field rettype added in             https://github.com/JuliaLang/julia/pull/54655
    # field has_image_globalref added in https://github.com/JuliaLang/julia/pull/57433
    # CodeInfo constructor. TODO: Should be in Core
    let
        fns = fieldnames(Core.CodeInfo)
        fts = fieldtypes(Core.CodeInfo)
        conversions = [:(convert($t, $n)) for (t,n) in zip(fts, fns)]

        expected_fns = (:code, :debuginfo, :ssavaluetypes, :ssaflags, :slotnames, :slotflags, :slottypes, :rettype, :parent, :edges, :min_world, :max_world, :method_for_inference_limit_heuristics, :nargs, :propagate_inbounds, :has_fcall, :has_image_globalref, :nospecializeinfer, :isva, :inlining, :constprop, :purity, :inlining_cost)
        expected_fts = (Vector{Any}, Core.DebugInfo, Any, Vector{UInt32}, Vector{Symbol}, Vector{UInt8}, Any, Any, Any, Any, UInt, UInt, Any, UInt, Bool, Bool, Bool, Bool, Bool, UInt8, UInt8, UInt16, UInt16)
        code = if fns != expected_fns || fts != expected_fts
            :(function _CodeInfo(args...)
                  error(string(
                      "JuliaLowering didn't recognize Core.CodeInfo's fields; ",
                      "it may need updating to match Core.CodeInfo.\n",
                      "expected field names: $($expected_fns)\n",
                      "expected field types: $($expected_fts)\n"))
              end)
        else
            :(function _CodeInfo($(fns...))
                $(Expr(:new, :(Core.CodeInfo), conversions...))
            end)
        end

        Core.eval(@__MODULE__, code)
    end
end

"""
Uncompressed form of DebugInfo's linetable::String.  When compressing, some
conveniences are erased:
- `file` is not present
- `line_offset` is identical
- `spans` pairs (s1, s2) are stored `(s1-byte_offset, s2-s1+1)`
- `line_starts` are stored `x-byte_offset`
"""
struct SourceByteTable
    file::Symbol
    line_offset::Int32
    spans::Vector{Tuple{Int32,Int32}}
    line_starts::Vector{Int32}
    function SourceByteTable(file, line_offset, spans, line_starts)
        @assert issorted(spans)
        @assert allunique(spans)
        @assert issorted(line_starts)
        @assert allunique(line_starts)
        @assert length(line_starts) > 0
        for s in spans
            @assert 0 < s[2] "linenode provenance; expected SourceFile"
            @assert 0 < s[1] <= s[2]+1
        end
        if !isempty(spans)
            @assert !isempty(line_starts)
            min_byte = spans[begin][begin]
            max_byte = maximum(last, spans)
            @assert line_starts[begin] <= min_byte
            for ls in line_starts[begin+1:end]
                @assert min_byte < ls
                @assert ls <= max_byte
            end
        else
            # Not used for now
            @assert false
        end

        new(file, line_offset, spans, line_starts)
    end
end
function SourceByteTable(sf::SourceFile, spans::Vector{Tuple{Int32, Int32}})
    # Trim all newlines outside SBT's range
    line_starts = map(ls->Int32(ls+sf.byte_offset), sf.line_starts)
    b0, _ = JuliaSyntax.source_line_range(sf, spans[1][1])
    first_line = sf.first_line
    while length(line_starts) >= 2 && line_starts[2] <= b0
        popfirst!(line_starts)
        first_line += 1
    end
    max_byte = maximum(last, spans)
    while !isempty(line_starts) && max_byte < line_starts[end]
        pop!(line_starts)
    end
    SourceByteTable(Symbol(sf.filename), first_line, spans, line_starts)
end

function _take32(io::IOBuffer, n::Integer)
    n in (0, 1, 2, 4) || throw(ArgumentError("Unsupported byte count"))
    v = Int32(0)
    n >= 1 && (v |= Int32(read(io, UInt8)))
    n >= 2 && (v |= Int32(read(io, UInt8))<<8)
    n >= 4 && (v |= Int32(read(io, UInt8))<<16)
    n >= 4 && (v |= Int32(read(io, UInt8))<<24)
    return v
end

function _push32(io::IOBuffer, v::Int32, n)
    n in (0, 1, 2, 4) || throw(ArgumentError("Unsupported byte count"))
    n >= 1 && write(io, v % UInt8)
    n >= 2 && write(io, (v>>>8) % UInt8)
    n >= 4 && write(io, (v>>>16) % UInt8)
    n >= 4 && write(io, (v>>>24) % UInt8)
    nothing
end

_encoded_len(max::Int32) = Int32(max == 0 ? 0 :
    max < typemax(UInt8) ? 1 :
    max < typemax(UInt16) ? 2 : 4)

function compress_sbt(sbt::SourceByteTable)
    min_byte = sbt.line_starts[1]
    max_byte = Int32(0)
    max_span = Int32(0)
    for (b1,b2) in sbt.spans
        max_span = max(max_span, (b2+Int32(1))-b1)
        max_byte = max(max_byte, b2)
    end

    max_byte_rel = Int32(min_byte >= max_byte ? 1 : (max_byte - min_byte))
    nlocs::Int32 = length(sbt.spans)
    encl_span = _encoded_len(max_span)
    encl_byte = _encoded_len(max_byte_rel)
    final_len = 14 + # header
        (encl_byte + encl_span) * nlocs +
        (encl_byte * length(sbt.line_starts))

    io = IOBuffer(;sizehint=final_len)
    _push32(io, min_byte, 4)
    _push32(io, sbt.line_offset, 4)
    _push32(io, nlocs, 4)
    _push32(io, encl_byte, 1)
    _push32(io, encl_span, 1)
    for (b1, b2) in sbt.spans
        _push32(io, b1 - min_byte, encl_byte)
        _push32(io, b2 - b1 + Int32(1), encl_span)
    end
    for n in sbt.line_starts
        _push32(io, n - min_byte, encl_byte)
    end

    out = take!(io)
    let l = length(out)
        @assert l == final_len "wrong final length $l"
    end
    return String(out)
end

function uncompress_sbt(di::Core.DebugInfo)
    di.linetable isa String || throw(ArgumentError("linetable: expected string"))
    io = IOBuffer(di.linetable)
    byte_offset = _take32(io, 4)
    line_offset = _take32(io, 4)
    nlocs = _take32(io, 4)
    byte_encl = _take32(io, 1)
    span_encl = _take32(io, 1)

    let newlines_offset = (byte_encl + span_encl) * nlocs
        @assert bytesavailable(io) >= newlines_offset "compressed string too short"
        @assert byte_encl == 0 ||
            (bytesavailable(io) - newlines_offset) % byte_encl == 0 "bad newlines"
    end

    out_spans = Tuple{Int32,Int32}[]
    for i in 1:nlocs
        s1 = _take32(io, byte_encl)
        s2 = _take32(io, span_encl)
        push!(out_spans, (s1+byte_offset, s1+byte_offset+s2-1))
    end

    out_newlines = Int32[]
    while bytesavailable(io) > 0
        push!(out_newlines, _take32(io, byte_encl) + byte_offset)
    end
    return SourceByteTable(di.def, line_offset, out_spans, out_newlines)
end

const LINENODE_SPAN_END = Int32(-5)

# Byte-precise `DebugInfo` requires `Core.DebugInfo` to accept a `String` linetable,
# which is only available on recent Julia.  On older versions (e.g. v1.12) we degrade to
# line-based `DebugInfo` so that lowering still produces a valid `CodeInfo`, at the cost of
# byte-precise source attribution.
const _has_byte_precise_debuginfo =
    hasmethod(Core.DebugInfo, Tuple{Symbol, String, Core.SimpleVector, String})

# Byte span (first, last) of the `line`th line within `sf`, or `nothing` if
# `line` is outside `sf`'s range.  Used to synthesize a positive, byte-precise
# span for statements whose only provenance is a bare `LineNumberNode` (e.g. a
# macro's `__source__`), so that they participate in byte-precise `DebugInfo`
# and land on their own textual line (matching flisp).
function _line_byte_span(sf::SourceFile, line::Integer)
    lineidx = Int(line) - sf.first_line + 1
    nls = length(sf.line_starts)
    (lineidx < 1 || lineidx > nls) && return nothing
    b1 = sf.line_starts[lineidx] + sf.byte_offset
    b2 = (lineidx < nls ? sf.line_starts[lineidx + 1] - 1 :
                          ncodeunits(sf.code)) + sf.byte_offset
    return (Int32(b1), Int32(max(b1, b2)))
end

# `true` when the source ref `x` (a `SourceRef` or `LineNumberNode`) points
# into `top_sf`, so `_di_pos` can express it as a position there.
function _ref_in_top_sf(x, top_sf)
    if top_sf isa SourceFile
        x isa SourceRef ? x.file[]::SourceFile === top_sf :
            (x.file === Symbol(JuliaSyntax.filename(top_sf)) &&
             _line_byte_span(top_sf, x.line) !== nothing)
    else # top_sf::Symbol: line-based debuginfo, match by filename
        x isa SourceRef ? Symbol(JuliaSyntax.filename(x.file[]::SourceFile)) === top_sf :
            x.file === top_sf
    end
end

# The source ref used for `st`'s debuginfo: `st`'s *own* provenance (nearest
# embedded line node — matching flisp's backtrace-line attribution for
# macro-generated code) when it points into `top_sf`; otherwise the nearest
# enclosing macrocall (climbing the macro-provenance chain outward) that does.
# Returns `nothing` if no ref along the chain points into `top_sf`.
#
# The single-file `DebugInfo` model can only express positions in `top_sf`, so
# content whose own provenance names a *foreign* file (e.g. a macro body
# defined in another file) is deliberately attributed to its macrocall site in
# `top_sf`; this keeps byte-precise debuginfo intact for such CodeInfos.
function _di_srcref(st::SyntaxTree, top_sf)
    x = JuliaSyntax.sourceref(st)
    _ref_in_top_sf(x, top_sf) && return x
    mp = JuliaSyntax.macro_prov(st)
    while !isnothing(mp)
        x = JuliaSyntax.sourceref(mp)
        _ref_in_top_sf(x, top_sf) && return x
        mp = JuliaSyntax.macro_prov(mp)
    end
    return nothing
end

function _di_pos(st::SyntaxTree, top_sf)
    src = _di_srcref(st, top_sf)
    # Fall back to the outermost macrocall for anomalous provenance (chain
    # entirely outside `top_sf`); callers with a better fallback (the parent
    # CodeInfo's position) check `_di_srcref` themselves first.
    src = src !== nothing ? src : JuliaSyntax.unexpanded_sourceref(st)
    @jl_assert (src isa SourceRef || src isa LineNumberNode) st
    if top_sf isa SourceFile
        if src isa SourceRef
            (Int32(first_byte(src)), Int32(last_byte(src)))
        else
            # Synthesize the line's byte span so `__source__`-style provenance
            # participates in byte-precise debuginfo.
            span = _ref_in_top_sf(src, top_sf) ?
                _line_byte_span(top_sf, src.line) : nothing
            span !== nothing ? span : (Int32(src.line), LINENODE_SPAN_END)
        end
    else
        # Line-based debuginfo: degrade any byte-precise ref to its line
        line = src isa SourceRef ? JuliaSyntax.source_line(src) : src.line
        (Int32(line), LINENODE_SPAN_END)
    end
end

# TODO sourcefile(::LNN) should return Symbol, not LNN
function _di_sourcefile(st)
    # if st.context.unexpanded isa SyntaxTree
    #     @jl_assert st.context.unexpanded._graph === st._graph (st, "bad unexpanded: different graph") (st.context.unexpanded, "this is the unexpanded tree")
    # end
    x = JuliaSyntax.unexpanded_sourceref(st)
    x isa LineNumberNode ? x.file : x.file[]::SourceFile
end

# A single pass over all IR to collect unique byte/line positions and CodeInfos
function collect_locs!(node_sources, codeinfos, top_sf, st)
    if kind(st) === K"code_info"
        push!(codeinfos, st)
        # TODO: macro_source is ignored for now
        get!(node_sources, st._id, _di_pos(st, top_sf))
        for c in children(st[1])
            node_sources[c._id] =
                if _di_srcref(c, top_sf) === nothing
                    # No provenance along `c`'s macro chain points into
                    # `top_sf` (not even its macrocall): genuinely
                    # inconsistent; attribute to the parent CodeInfo.
                    top_sf isa SourceFile &&
                        @warn "inconsistent provenance for child" c st
                    node_sources[st._id]
                else
                    _di_pos(c, top_sf)
                end
            collect_locs!(node_sources, codeinfos, top_sf, c)
        end
    elseif !is_leaf(st)
        # Non-toplevel codeinfo can contain nested codeinfo (opaque closures)
        for c in children(st)
            collect_locs!(node_sources, codeinfos, top_sf, c)
        end
    end
    nothing
end

# (filename, line) of a source ref, for the macro-expansion edge chain, or
# `nothing` for a file-less `LineNumberNode` (which, like flisp, only updates
# the line within the enclosing file and so introduces no macro boundary).
function _ref_file_line(x)
    if x isa SourceRef
        (Symbol(JuliaSyntax.filename(x.file[]::SourceFile)), Int32(JuliaSyntax.source_line(x)))
    elseif x.file === nothing
        nothing
    else
        (x.file::Symbol, Int32(x.line))
    end
end

# The nested "macro expansion" frames for statement `c`, one per file boundary
# its provenance crossed, shallowest (nearest the enclosing scope) first.
#
# flisp marks macro expansion with `push_loc`/`pop_loc` whenever a lowered block
# enters source from a different file, producing a stack of file-keyed
# `DebugInfo` edges rendered as `"macro expansion"` frames (`method.c`
# `jl_linetable_to_debuginfo`). JL reconstructs the same stack from each
# statement's provenance chain: `sourceref(c)` climbing `macro_prov` outward,
# with consecutive same-file levels merged. The outermost in-`top_sf` level is
# the statement's own byte-precise location (the top codeloc), so edges are the
# levels inside it. Returns `(shallow->deep)` `(file, line)` pairs, empty when
# `c` was not macro-expanded across a file boundary.
function _macro_edge_groups(c::SyntaxTree, topfile::Symbol)
    groups = Tuple{Symbol,Int32}[]
    push_group!(x) = let fl = _ref_file_line(x)
        if fl !== nothing
            (f, l) = fl
            (!isempty(groups) && groups[end][1] === f) ? (groups[end] = (f, l)) :
                push!(groups, (f, l))
        end
    end
    push_group!(JuliaSyntax.sourceref(c))
    mp = JuliaSyntax.macro_prov(c)
    while mp !== nothing
        push_group!(JuliaSyntax.sourceref(mp))
        mp = JuliaSyntax.macro_prov(mp)
    end
    # The top codeloc represents the outermost `topfile` level; edges are the
    # levels inside it. No in-file level (fully foreign provenance) is handled
    # as parent attribution by `collect_locs!`, so emit no edges here.
    #
    # A synthetic-context thunk (`eval` of a hand-built `Expr`, file `:none`)
    # has no source file of its own: its outermost provenance level is the top
    # codeloc whatever file it names (`:none` itself, or a real file the code
    # was quoted from), and every inner level is a `push_loc` macro-expansion
    # frame -- exactly as flisp does.  Root at the outermost level rather than
    # searching for a `:none` group (which real quoted content never carries,
    # so the search would drop all its frames).
    root = topfile === :none ? (isempty(groups) ? nothing : lastindex(groups)) :
                               findlast(g -> g[1] === topfile, groups)
    (root === nothing || root == 1) && return Tuple{Symbol,Int32}[]
    return [groups[i] for i in (root-1):-1:1]
end

# Nested macro-expansion edge under construction, mirroring `method.c`'s
# per-file `edge`/`edge_list2` arraylists.
mutable struct DebugInfoEdge
    file::Symbol
    children::Vector{DebugInfoEdge}
    locs::Vector{Tuple{Int32,Int32,Int32}} # (line, edge_index, edge_pc)
end
DebugInfoEdge(file::Symbol) = DebugInfoEdge(file, DebugInfoEdge[], Tuple{Int32,Int32,Int32}[])

# Register `rest[i:end]` (shallow->deep) into the file-keyed edge list, returning
# this statement's `(edge_index, edge_pc)` (both 1-based).  Mirror of `add_edge`.
function add_edge!(edges::Vector{DebugInfoEdge}, rest::Vector{Tuple{Symbol,Int32}}, i::Int)
    file, line = rest[i]
    ei = findfirst(e -> e.file === file, edges)
    if ei === nothing
        push!(edges, DebugInfoEdge(file))
        ei = length(edges)
    end
    edge = edges[ei]
    to = Int32(0); pc = Int32(0)
    if i < length(rest)
        to, pc = add_edge!(edge.children, rest, i + 1)
    end
    loc = (line, to, pc)
    li = findfirst(==(loc), edge.locs)
    if li === nothing
        push!(edge.locs, loc)
        li = length(edge.locs)
    end
    return (Int32(ei), Int32(li))
end

# Convert the edge builders into the `Core.DebugInfo` svec.  Mirror of `alloc_edges`.
function build_edges(edges::Vector{DebugInfoEdge})
    isempty(edges) && return Core.svec()
    out = Vector{Any}(undef, length(edges))
    for (i, e) in enumerate(edges)
        nlocs = length(e.locs)
        locs = Vector{Int32}(undef, 3*nlocs)
        for (j, (line, to, pc)) in enumerate(e.locs)
            locs[3j-2] = line; locs[3j-1] = to; locs[3j] = pc
        end
        out[i] = Core.DebugInfo(e.file, nothing, build_edges(e.children),
            @ccall(jl_compress_codelocs((0)::Int32, locs::Any, nlocs::Csize_t)::String))
    end
    return Core.svec(out...)
end

function add_ci_debuginfo!(st::SyntaxTree, file::Symbol, groupfile::Symbol,
                           top_sbt::Union{String, Nothing},
                           node_sources::Dict{NodeId, Tuple{Int32, Int32}},
                           spans::Vector{Tuple{Int32, Int32}})
    @jl_assert kind(st) === K"code_info" st
    stmts = children(st[1])
    # Per-statement macro-expansion frames, plus a per-region "anchor" for the
    # top codeloc.  flisp holds the root codeloc of every statement inside a
    # macro expansion at the region's first in-file line (the root-level
    # current line never advances inside a `push_loc` region); the statement's
    # own location lives in the deepest edge instead.  Mirror that by anchoring
    # all edge-carrying statements of one outermost macrocall at the textually
    # first in-file own provenance among them (falling back to the statement's
    # own position when the region has none).
    stmt_edges = Vector{Vector{Tuple{Symbol,Int32}}}(undef, length(stmts))
    regions = zeros(NodeId, length(stmts))
    anchors = Dict{NodeId, Tuple{Int32, Int32}}()
    for (i, c) in enumerate(stmts)
        rest = _macro_edge_groups(c, groupfile)
        stmt_edges[i] = rest
        isempty(rest) && continue
        mp = JuliaSyntax.macro_prov_end(c)
        mp === nothing && continue
        regions[i] = mp._id
        fl = _ref_file_line(JuliaSyntax.sourceref(c))
        if fl !== nothing && fl[1] === groupfile
            pos = node_sources[c._id]
            anchors[mp._id] = min(get(anchors, mp._id, pos), pos)
        end
    end
    edges = DebugInfoEdge[]
    locs = let a = sizehint!(Vector{Int32}(), 3*length(stmts))
        for (i, c) in enumerate(stmts)
            rest = stmt_edges[i]
            pos = isempty(rest) ? node_sources[c._id] :
                get(anchors, regions[i], node_sources[c._id])
            if top_sbt isa String # precise provenance
                push!(a, Int32(searchsortedfirst(spans, pos)))
            else
                j = searchsortedfirst(spans, pos)
                @jl_assert spans[j][2] == LINENODE_SPAN_END (c, "lno with span end?")
                push!(a, spans[j][1])
            end
            if isempty(rest)
                push!(a, Int32(0)); push!(a, Int32(0))
            else
                to, pc = add_edge!(edges, rest, 1)
                push!(a, to); push!(a, pc)
            end
        end
        a
    end

    setattr!(st, :debuginfo, Core.DebugInfo(
        file, top_sbt, build_edges(edges),
        @ccall(jl_compress_codelocs((-1)::Int32, locs::Any,
                                    numchildren(st[1])::Csize_t)::String)))
end

# First (file, line) with a real file inside `st`'s subtree provenance, also
# checking `K"Value"`-wrapped `LineNumberNode`s (a quoted block's line nodes,
# or a macrocall's location slot); `nothing` if there is none.
function _first_real_file_ref(st::SyntaxTree)
    x = JuliaSyntax.sourceref(st)
    if x isa SourceRef
        return (Symbol(JuliaSyntax.filename(x.file[]::SourceFile)),
                Int32(JuliaSyntax.source_line(x)))
    elseif x isa LineNumberNode && !(x.file === nothing || x.file === :none)
        return (x.file::Symbol, Int32(x.line))
    end
    if kind(st) === K"Value"
        v = st.value
        v isa LineNumberNode && !(v.file === nothing || v.file === :none) &&
            return (v.file::Symbol, Int32(v.line))
    end
    if !is_leaf(st)
        for c in children(st)
            r = _first_real_file_ref(c)
            r !== nothing && return r
        end
    end
    return nothing
end

# The (file, line) flisp would locate a synthetic-context thunk at: the first
# real-file line node inside the pre-expansion code -- in practice the
# `__source__` slot or quoted arguments of the outermost macrocall.
function _thunk_alt_source(codeinfos)
    isempty(codeinfos) && return nothing
    for c in children(codeinfos[1][1])
        mp = JuliaSyntax.macro_prov_end(c)
        mp === nothing && continue
        return _first_real_file_ref(mp)
    end
    return nothing
end

# Populate `.debuginfo` on all K"code_info" in `st`
function add_debuginfo!(st::SyntaxTree)
    @jl_assert kind(st) === K"code_info" st
    node_sources = Dict{NodeId, Tuple{Int32, Int32}}()
    codeinfos = SyntaxList(st._graph)
    top_sf = _di_sourcefile(st)
    collect_locs!(node_sources, codeinfos, top_sf, st)
    # A thunk lowered in a synthetic context (`eval` of a hand-built Expr:
    # file "none") is still located by flisp at the first real-file line node
    # inside the code (`jl_linetable_to_debuginfo`'s root entry).  Mirror
    # that: adopt that ref as the file and constant root line for the whole
    # thunk; the synthetic name still keys the macro-expansion edge grouping.
    alt = top_sf === nothing ||
          (!(top_sf isa SourceFile) && Symbol(top_sf) === :none) ?
        _thunk_alt_source(codeinfos) : nothing
    if alt !== nothing
        for id in collect(keys(node_sources))
            node_sources[id] = (alt[2], LINENODE_SPAN_END)
        end
    end
    byte_precise = _has_byte_precise_debuginfo && top_sf isa SourceFile
    if !byte_precise && top_sf isa SourceFile
        # Without byte-precise support, degrade each byte span to its line number
        # so the line-based path below emits valid `DebugInfo` (same shape as the
        # `LineNumberNode` case).
        for id in collect(keys(node_sources))
            node_sources[id][2] == LINENODE_SPAN_END && continue
            line = Int32(JuliaSyntax.source_line(top_sf, node_sources[id][1]))
            node_sources[id] = (line, LINENODE_SPAN_END)
        end
    end
    spans = sort!(unique(values(node_sources)))
    if byte_precise
        top_sbt = compress_sbt(SourceByteTable(top_sf, spans))
        file = Symbol(top_sf.filename)
    else
        top_sbt = nothing
        file = top_sf isa SourceFile ? Symbol(top_sf.filename) :
               Symbol(something(top_sf, :none))
    end
    groupfile = file
    alt === nothing || (file = alt[1])
    for ci in codeinfos
        add_ci_debuginfo!(ci, file, groupfile, top_sbt, node_sources, spans)
    end
end

# flisp: jl_new_code_info_from_ir (method.c)
function compute_ssaflags(st::SyntaxTree)
    @jl_assert kind(st) == K"block" st
    stmts = children(st)
    out = zeros(UInt32, length(stmts))
    inline_flags = Vector{Bool}()
    inbounds_depth = 0
    purity_flags = Vector{UInt32}()

    # Note this should probably go in validation or be a user-facing
    # loweringerror, but method.c only checks this in asserts builds, so we may
    # need to allow these to be unbalanced
    function checked_pop!(stk)
        @jl_assert(!isempty(stk), (st, "ssaflags pop without push"))
        pop!(stk)
    end
    for (i, stmt) in enumerate(stmts)
        is_flag_stmt = true
        @stm stmt begin
            [K"inbounds" [K"Value"]] -> stmt[1].value::Bool ?
                (inbounds_depth += 1) : # push
                (inbounds_depth = 0)    # clear
            [K"inbounds_pop"] -> (inbounds_depth = max(0, inbounds_depth-1))
            [K"boundscheck" _...] -> nothing
            [K"inline" [K"Value"]] -> stmt[1].value::Bool ?
                push!(inline_flags, true) : checked_pop!(inline_flags)
            [K"noinline" [K"Value"]] -> stmt[1].value::Bool ?
                push!(inline_flags, false) : checked_pop!(inline_flags)
            [K"purity"] -> checked_pop!(purity_flags)
            [K"purity" _ _...] -> push!(
                purity_flags,
                UInt32(purity_expr_to_flags(stmt)) << Core.Compiler.NUM_IR_FLAGS)
            _ -> is_flag_stmt = false
        end
        flag = UInt32(0)
        if !isempty(inline_flags)
            flag |= (inline_flags[end] ?
                Core.Compiler.IR_FLAG_INLINE : Core.Compiler.IR_FLAG_NOINLINE)
        end
        if inbounds_depth != 0
            flag |= Core.Compiler.IR_FLAG_INBOUNDS
        end
        if !isempty(purity_flags)
            for pf in purity_flags
                flag |= pf
            end
        end
        out[i] = is_flag_stmt ? UInt32(0) : flag
    end
    @jl_assert length(out) == length(stmts) st
    @jl_assert length(inline_flags) == 0 st
    @jl_assert length(purity_flags) == 0 st
    out
end

# Convert SyntaxTree to the CodeInfo+Expr data structures understood by the
# Julia runtime
function to_code_info(ex::SyntaxTree, slots::Vector{Slot}, meta::CompileHints)
    nargs = sum((s.kind==:argument for s in slots), init=0)
    slotnames = Vector{Symbol}(undef, length(slots))
    slot_rename_inds = Dict{String,Int}()
    slotflags = Vector{UInt8}(undef, length(slots))
    for (i, slot) in enumerate(slots)
        name = slot.name
        # TODO: Do we actually want unique names here? The C code in
        # `jl_new_code_info_from_ir` has logic to simplify gensym'd names and
        # use the empty string for compiler-generated bindings.
        if name !== UNUSED
            ni = get(slot_rename_inds, name, 0)
            slot_rename_inds[name] = ni + 1
            if ni > 0
                name = "$name@$ni"
            end
        end
        sname = Symbol(name)
        slotnames[i] = sname
        slotflags[i] =                   # Inference          | Codegen
            slot.is_read          << 3 | # SLOT_USED          | jl_vinfo_sa
            slot.is_single_assign << 4 | # SLOT_ASSIGNEDONCE  | -
            slot.is_maybe_undef   << 5 | # SLOT_USEDUNDEF     | jl_vinfo_usedundef
            slot.is_called        << 6   # SLOT_CALLED        | -
    end

    stmts = map(_to_lowered_expr, children(ex[1]))
    has_image_globalref = any(codeinfo_has_image_globalref, stmts)
    ssaflags = compute_ssaflags(ex[1])
    propagate_inbounds =
        get(meta, :propagate_inbounds, false)
    has_fcall = any(codeinfo_has_fcall, stmts)
    nospecializeinfer =
        get(meta, :nospecializeinfer, false)
    inlining =
        get(meta, :inline, false) ? 0x01 :
        get(meta, :noinline, false) ? 0x02 : 0x00
    constprop =
        get(meta, :aggressive_constprop, false) ? 0x01 :
        get(meta, :no_constprop, false) ? 0x02 : 0x00
    purity =
        let eo = get(meta, :purity, nothing)
            isnothing(eo) ? 0x0000 : eo::UInt16
        end

    # The following CodeInfo fields always get their default values for
    # uninferred code.
    ssavaluetypes      = length(stmts) # Why does the runtime code do this?
    slottypes          = nothing
    parent             = nothing
    method_for_inference_limit_heuristics = nothing
    edges               = nothing
    min_world           = Csize_t(1)
    max_world           = typemax(Csize_t)
    isva                = false
    inlining_cost       = 0xffff
    rettype             = Any

    @jl_assert(length(stmts) == numchildren(ex[1]), ex)

    _CodeInfo(
        stmts,
        ex.debuginfo,
        ssavaluetypes,
        ssaflags,
        slotnames,
        slotflags,
        slottypes,
        rettype,
        parent,
        edges,
        min_world,
        max_world,
        method_for_inference_limit_heuristics,
        nargs,
        propagate_inbounds,
        has_fcall,
        has_image_globalref,
        nospecializeinfer,
        isva,
        inlining,
        constprop,
        purity,
        inlining_cost
    )
end

@fzone "JL: to_lowered_expr" function to_lowered_expr(ex::SyntaxTree)
    ensure_attributes!(ex._graph; debuginfo=Any)
    add_debuginfo!(ex)
    _to_lowered_expr(ex)
end

function _to_lowered_expr(ex::SyntaxTree)
    k = kind(ex)
    if is_literal(k)
        ex.value
    elseif k == K"nothing"
        nothing
    elseif k == K"core"
        GlobalRef(Core, Symbol(ex.name_val::String))
    elseif k == K"top"
        GlobalRef(Base, Symbol(ex.name_val::String))
    elseif k == K"globalref"
        GlobalRef(ex.mod::Module, Symbol(ex.name_val::String))
    elseif k == K"Identifier"
        # TODO: assert false (only reachable from simdloop?)
        Symbol(ex.name_val::String)
    elseif k == K"SourceLocation"
        QuoteNode(source_location(LineNumberNode, ex))
    elseif k == K"Symbol"
        QuoteNode(Symbol(ex.name_val::String))
    elseif k == K"slot"
        Core.SlotNumber(ex.var_id::IdTag)
    elseif k == K"static_parameter"
        Expr(:static_parameter, ex.var_id::IdTag)
    elseif k == K"SSAValue"
        Core.SSAValue(ex.var_id::IdTag)
    elseif k == K"return"
        v = _to_lowered_expr(ex[1])
        @jl_assert Base.Compiler.is_valid_return(v) ex
        Core.ReturnNode(v)
    elseif k == K"inert"
        est_to_expr(ex)
    elseif k == K"syntaxinert"
        ex[1]
    elseif k == K"code_info"
        ir = to_code_info(ex, ex.slots, ex.meta)
        if ex.is_toplevel_thunk
            Expr(:thunk, ir) # TODO: Maybe nice to just return a CodeInfo here?
        else
            ir
        end
    elseif k == K"Value"
        @jl_assert !isa_lowering_ast_node(ex.value) (
            ex, string("smuggling AST through Value is asking for trouble; ",
                       "find a SyntaxTree representation"))
        ex.value isa LineNumberNode ? QuoteNode(ex.value) : ex.value
    elseif k == K"goto"
        Core.GotoNode(ex[1].id)
    elseif k == K"gotoifnot"
        Core.GotoIfNot(_to_lowered_expr(ex[1]), ex[2].id)
    elseif k == K"enter"
        catch_idx = ex[1].id
        numchildren(ex) == 1 ?
            Core.EnterNode(catch_idx) :
            Core.EnterNode(catch_idx, _to_lowered_expr(ex[2]))
    elseif k == K"method"
        cs = map(_to_lowered_expr, children(ex))
        # Ad-hoc unwrapping to satisfy `Expr(:method)` expectations
        cs1 = cs[1]
        c1 = cs1 isa QuoteNode ? cs1.value : cs1
        Expr(:method, c1, cs[2:end]...)
    elseif k == K"newvar"
        Core.NewvarNode(_to_lowered_expr(ex[1]))
    elseif k == K"opaque_closure_method"
        args = map(_to_lowered_expr, children(ex))
        # opaque_closure_method has special non-evaluated semantics for the
        # `functionloc` line number node so we need to undo a level of quoting
        arg4 = args[4]
        @jl_assert arg4 isa QuoteNode ex
        args[4] = arg4.value
        Expr(:opaque_closure_method, args...)
    elseif k == K"meta"
        args = Any[_to_lowered_expr(e) for e in children(ex)]
        # Unpack K"Symbol" QuoteNode as `Expr(:meta)` requires an identifier here.
        arg1 = args[1]
        @jl_assert (arg1 isa QuoteNode) ex
        args[1] = arg1.value
        Expr(:meta, args...)
    elseif k == K"foreignsymbol"
        @jl_assert kind(ex[1]) == K"tuple" ex
        _foreignsymbol_expr(ex[1])
    elseif k == K"static_eval"
        @jl_assert numchildren(ex) == 1 ex
        _to_lowered_expr(ex[1])
    elseif k == K"cfunction"
        # For a scope-resolved callable (`K"static_eval"`), drop the module tag
        # and emit a bare Symbol so `method.c` resolves it in the method's
        # module at eval time, matching Base `@cfunction`'s runtime semantics.
        ret = Expr(:cfunction)
        for (i, e) in enumerate(children(ex))
            if i == 2 && kind(e) == K"static_eval" && kind(e[1]) == K"globalref"
                push!(ret.args, QuoteNode(Symbol(e[1].name_val::String)))
            else
                push!(ret.args, _to_lowered_expr(e))
            end
        end
        return ret
    elseif k in KSet"inline noinline inbounds inbounds_pop purity"
        # only used in compute_ssaflags (see method.c)
        nothing
    else
        # Allowed forms according to https://docs.julialang.org/en/v1/devdocs/ast/
        #
        # call invoke static_parameter `=` method struct_type abstract_type
        # primitive_type global const new splatnew isdefined
        # enter leave pop_exception inbounds boundscheck loopinfo copyast meta
        # lambda
        head = k == K"call"      ? :call       :
               k == K"new"       ? :new        :
               k == K"splatnew"  ? :splatnew   :
               k == K"="         ? :(=)        :
               k == K"leave"     ? :leave      :
               k == K"isdefined" ? :isdefined  :
               k == K"loopinfo"  ? :loopinfo   :
               k == K"boundscheck"       ? :boundscheck       :
               k == K"latestworld"       ? :latestworld       :
               k == K"pop_exception"     ? :pop_exception     :
               k == K"captured_local"    ? :captured_local    :
               k == K"gc_preserve_begin" ? :gc_preserve_begin :
               k == K"gc_preserve_end"   ? :gc_preserve_end   :
               k == K"foreigncall"       ? :foreigncall       :
               k == K"foreignglobal"     ? :foreignglobal     :
               k == K"cfunction"         ? :cfunction         :
               k == K"aliasscope"        ? :aliasscope        :
               k == K"popaliasscope"     ? :popaliasscope     :
               k == K"new_opaque_closure" ? :new_opaque_closure :
               nothing
        if isnothing(head)
            throw(LoweringError(ex, "Unhandled form for kind $k"))
        end
        ret = Expr(head)
        for e in children(ex)
            push!(ret.args, _to_lowered_expr(e))
        end
        return ret
    end
end

# ultra-permissive conversion allowing unlowered structure, but lowered leaves
function _foreignsymbol_expr(ex)
    if is_leaf(ex) || kind(ex) == K"inert"
        _to_lowered_expr(ex)
    else
        k = kind(ex)
        Expr(Symbol((k === K"unknown_head" ? ex.name_val : untokenize(k))::String),
             map(_foreignsymbol_expr, children(ex))...)
    end
end

#-------------------------------------------------------------------------------
# Our version of eval - should be upstreamed though?
@fzone "JL: eval" function eval(mod::Module, @nospecialize(ex);
                                soft_scope::Union{Nothing,Bool}=nothing,
                                expr_compat_mode::Bool=false)
    # Run the `eval` driver in the lowering world. Any internal operations
    # are required to `invokelatest` before executing any code that dispatches
    # on user code / types.
    ver = expr_compat_mode ? JL_OLD_SYNTAX_VERSION : JL_NEW_SYNTAX_VERSION
    return invoke_in_lowering_world(_lower_and_eval, mod, ex, ver, soft_scope)
end

# Render an `internal=false` `LoweringError` (bad user code -- the JuliaLowering
# analogue of flisp's `Expr(:error, msg)` sentinel; see the `LoweringError`
# docstring) into a plain message string, mirroring flisp's lowering-error
# message. Source location is appended in flisp's `format-loc` style
# (" around file:line") when available.
function _lowering_error_message(exc::LoweringError)
    io = IOBuffer()
    for i in eachindex(exc.msgs)
        i > 1 && print(io, '\n')
        print(io, exc.msgs[i])
        lnn = try
            source_location(LineNumberNode, exc.sts[i])
        catch
            nothing
        end
        if lnn isa LineNumberNode && lnn.line != 0 &&
                lnn.file !== :none && lnn.file !== nothing
            print(io, " around ", lnn.file, ":", lnn.line)
        end
    end
    return String(take!(io))
end

# Wrap a `MacroExpansionError` (a macro that threw while being expanded) in a
# `LoadError`, matching flisp: `jl_invoke_julia_macro` wraps any exception from
# a macro body in `LoadError(file, line, err)` on the real top-level-lowering
# path (its `throw_load_error` flag; `src/ast.c`). Packages assert this via the
# standard `@test_throws LoadError @eval @somemacro(bad)` idiom.
#
# flisp wraps the macro body's *original* thrown value directly (`LoadError`'s
# `.error` is whatever the macro threw -- an `ErrorException`, `ArgumentError`,
# a bare non-`Exception` value, even a `LoadError` the macro itself threw), with
# no wrapper type of its own. `MacroExpansionError` is JuliaLowering's richer
# *introspection*-facing representation, but on this flisp-compat boundary we
# must reproduce flisp's observable exactly, so packages that assert the type,
# message, or fields of `ex.error` keep working (found via Match.jl in PkgEval).
# Unwrap down to that original value, descending through nested
# `MacroExpansionError`s (a macro whose body expands another failing macro) to
# the innermost recorded cause. `JuliaLowering.macroexpand`'s introspection path
# does not go through here and keeps the raw `MacroExpansionError`.
function _macroexpansion_loaderror(exc::MacroExpansionError,
                                   fallback::LineNumberNode=LineNumberNode(0, :none))
    lnn = fallback
    try
        # Location comes from the (outermost) erroring macrocall, as flisp takes
        # it from that macrocall's `LineNumberNode` -- not from the innermost
        # cause, which may originate in an unrelated file.
        l = source_location(LineNumberNode, exc.ex)
        if l isa LineNumberNode && l.line != 0
            lnn = l
        end
    catch
    end
    file = lnn.file === nothing ? "none" : String(lnn.file)
    # Unwrap to the innermost cause, as flisp wraps the macro's original
    # exception. A user-thrown MacroExpansionError carrying its own `err` is
    # indistinguishable from machinery wrapping and is unwrapped too.
    inner = exc
    while inner isa MacroExpansionError && inner.err !== nothing
        inner = inner.err
    end
    return LoadError(file, lnn.line, inner)
end

# Total version of the above for use on exception-reporting paths: the
# `LoadError` conversion is diagnostic shaping only, so if it ever throws (it
# is believed total today -- `source_location` is guarded and
# `LineNumberNode.file` is constructor-checked to `Union{Nothing,Symbol}` --
# but future edits could regress that), surface the original error rather than
# masking it with the conversion's own exception. `convert_exc` exists for
# dependency injection in tests.
function _macroexpansion_loaderror_total(exc::MacroExpansionError,
                                         fallback::LineNumberNode,
                                         convert_exc::F=_macroexpansion_loaderror) where {F}
    try
        convert_exc(exc, fallback)
    catch
        exc
    end
end

# flisp-compatible `eval` used by the `@eval` macro. Behaves like `eval`, but
# restores flisp's user-facing error contract at the top-level-eval boundary
# (there `@eval` expands to `Core.eval`):
#
# * a user-facing (`internal=false`) `LoweringError` surfaces as an ordinary
#   `ErrorException` (`LoweringError` is `<: Exception` but not `<:
#   ErrorException`, silently breaking `@test_throws ErrorException @eval(bad)`
#   for syntax/lowering errors -- found via DataPipes); and
# * a `MacroExpansionError` (a macro erroring during expansion) is wrapped in
#   `LoadError`, as flisp's macro-invocation path does (breaking
#   `@test_throws LoadError @eval @somemacro(bad)` -- found via StationXML /
#   StrLiterals).
#
# Both conversions live here, on the `@eval` path, and are mirrored in
# `core_lowering_hook` -- the `Core._lower` hook underlying plain
# `eval`/`include`/toplevel code -- which performs the same
# `MacroExpansionError`->`LoadError` and non-internal
# `LoweringError`->`ErrorException` conversions so every top-level-eval entry
# point honors flisp's contract, not just explicit `@eval`. They live here (and
# in the hook) rather than in `eval` itself: `eval`/`include_string`/`lower` are
# JuliaLowering's programmatic API and its own test suite asserts the richer
# `LoweringError`/`MacroExpansionError` through them, so they must keep raising
# them (mirroring flisp's introspection-only `macroexpand`, which does not
# wrap). `internal` (assertion-class) `LoweringError`s stay loud everywhere.
function eval_flisp_compat(mod::Module, @nospecialize(ex);
                           soft_scope::Union{Nothing,Bool}=nothing,
                           expr_compat_mode::Bool=false)
    try
        return eval(mod, ex; soft_scope, expr_compat_mode)
    catch exc
        if exc isa MacroExpansionError
            throw(_macroexpansion_loaderror_total(exc, LineNumberNode(0, :none)))
        elseif exc isa LoweringError && !exc.internal
            throw(ErrorException(_lowering_error_message(exc)))
        end
        rethrow()
    end
end

# `ex` may be a `SyntaxTree` or an `Expr` (or `Expr` tree leaves of any type).
function _lower_and_eval(mod::Module, @nospecialize(ex), ver::VersionNumber,
                         soft_scope::Union{Nothing,Bool})
    st = ex isa SyntaxTree ? ex : expr_to_est(ex)
    iter = lower_init(st, ver)
    return _eval(mod, iter; soft_scope)
end

function _eval(mod::Module, iter::LoweringIterator; soft_scope::Union{Nothing,Bool}=nothing)
    modules = Module[mod]
    result = nothing
    while true
        thunk = lower_step(iter, modules[end], Base.get_world_counter(); soft_scope)::Core.SimpleVector
        type = thunk[1]::Symbol
        if type == :done
            break
        elseif type == :begin_module
            filename = something(thunk[5].file, :none)
            mod = @ccall jl_begin_new_module(
                modules[end]::Any, thunk[3]::Symbol, thunk[2]::Any, thunk[4]::Cint,
                filename::Cstring, thunk[5].line::Cint)::Module
            push!(modules, mod)
        elseif type == :end_module
            @ccall jl_end_new_module(modules[end]::Module)::Cvoid
            result = pop!(modules)
        else
            @assert type == :thunk
            result = Base.invokelatest(Core.eval, modules[end], thunk[2])
        end
    end
    @assert length(modules) === 1
    return result
end

"""
    include(mod::Module, path::AbstractString)

Evaluate the contents of the input source file in the global scope of module
`mod`. Every module (except those defined with baremodule) has its own
definition of `include()` omitting the `mod` argument, which evaluates the file
in that module. Returns the result of the last evaluated expression of the
input file. During including, a task-local include path is set to the directory
containing the file. Nested calls to include will search relative to that path.
This function is typically used to load source interactively, or to combine
files in packages that are broken into multiple source files.
"""
function include(mod::Module, path::AbstractString)
    path, prev = Base._include_dependency(mod, path)
    code = read(path, String)
    tls = task_local_storage()
    tls[:SOURCE_PATH] = path
    try
        return include_string(mod, code, path)
    finally
        if prev === nothing
            delete!(tls, :SOURCE_PATH)
        else
            tls[:SOURCE_PATH] = prev
        end
    end
end

"""
    include_string(mod::Module, code::AbstractString, filename::AbstractString="string")

Like `include`, except reads code from the given string rather than from a file.
"""
function include_string(mod::Module, code::AbstractString, filename::AbstractString="string";
                        expr_compat_mode=false, version::VersionNumber=VERSION)
    eval(mod, parseall(SyntaxTree, code; filename, version); expr_compat_mode)
end

include(path::AbstractString) = include(JuliaLowering, path)
