# One per pass
struct MacroExpansionContext{Attrs} <: AbstractLoweringContext
    graph::SyntaxGraph{Attrs}
    syntax_context::SyntaxContext
    known_layers::Dict{ScopeLayer, Bool}
    world::UInt
    recursive::Bool
end

function MacroExpansionContext(st, world, recursive)
    sc = st.context::SyntaxContext
    MacroExpansionContext(
        st._graph, sc, Dict{ScopeLayer, Bool}(base_layer(sc)=>true),
        world, recursive)
end

function collect_unquoted!(ctx, unquoted, ex, depth)
    if kind(ex) == K"$" && depth == 0
        # children(ex) is usually length 1, but for double interpolation it may
        # be longer and the children may contain K"..." expressions. Wrapping
        # in a tuple groups the arguments together correctly in those cases.
        push!(unquoted, @ast ctx ex [K"tuple" children(ex)...])
    else
        inner_depth = kind(ex) == K"quote" ? depth + 1 :
                      kind(ex) == K"$"     ? depth - 1 :
                      depth
        for e in children(ex)
            collect_unquoted!(ctx, unquoted, e, inner_depth)
        end
    end
    return unquoted
end

# TODO: Implementing interpolations with a macro could give us better provenance
function expand_quote(ctx, st)
    unquoted = SyntaxList(ctx)
    collect_unquoted!(ctx, unquoted, st, 0)
    # not just optimizations; expected e.g. in `(. mod (quote field))`
    if is_expr_value(st)
        @jl_assert isempty(unquoted) st
        st
    elseif kind(st) === K"$"
        numchildren(st) != 1 && throw(LoweringError(
            st, raw"More than one value in bare `$` expression"))
        kind(st[1]) === K"..." && throw(LoweringError(
            st, raw"unexpected `...` in bare `$` expression"))
        @ast ctx st st[1]
    elseif kind(st) === K"Identifier" && !hasattr(st, :mod)
        @jl_assert isempty(unquoted) st
        @ast ctx st [K"inert" st]
    else
        @ast ctx st [K"call" interpolate_expr::K"Value" [K"inert" st] unquoted...]
    end
end

function collect_syntaxunquote!(ctx, unquoted, st, depth)
    if kind(st) === K"syntaxunquote" && depth == 0
        numchildren(st) !== 1 && throw(LoweringError(st, "malformed syntaxunquote"))
        push!(unquoted, @ast ctx st[1] [K"tuple" st[1]])
    else
        inner_depth = kind(st) == K"syntaxquote" ? depth + 1 :
                      kind(st) == K"syntaxunquote" ? depth - 1 : depth
        for c in children(st)
            collect_syntaxunquote!(ctx, unquoted, c, inner_depth)
        end
    end
    unquoted
end

# compared to quote: (1) no need for a copy when no unquotes, since output
# should be immutable.  (2) we do not optimize (syntaxquote (syntaxunquote x))
# -> x, since x may not be a SyntaxTree
function expand_syntaxquote(ctx, st)
    if kind(st) === K"syntaxunquote"
        numchildren(st) != 1 && throw(LoweringError(
            st, raw"More than one value in bare `syntaxunquote` expression"))
        kind(st[1]) === K"..." && throw(LoweringError(
            st, raw"unexpected `...` in bare `syntaxunquote` expression"))
    end
    unquoted = collect_syntaxunquote!(ctx, SyntaxList(ctx), st, 0)
    length(unquoted) == 0 ? @ast(ctx, st, [K"syntaxinert" st]) :
        @ast ctx st [K"call" interpolate_syntax::K"Value"
                 [K"syntaxinert" st] unquoted...]
end

# Passed to the user as an implicit macro argument
struct MacroContext{Attrs} <: AbstractLoweringContext
    graph::SyntaxGraph
    macrocall::SyntaxTree{Attrs}
end

struct MacroExpansionError <: Exception
    context::Union{Nothing,MacroContext}
    ex::SyntaxTree
    msg::String
    "The source position relative to the node - may be `:begin` or `:end` or `:all`"
    position::Symbol
    "Error that occurred inside the macro function call (`nothing` if no inner exception)"
    err
    MacroExpansionError(
        context::Union{Nothing,MacroContext}, ex::SyntaxTree, msg::AbstractString, position::Symbol,
        @nospecialize err = nothing
    ) = new(context, ex, msg, position, err)
end

function MacroExpansionError(ex::SyntaxTree, msg::AbstractString; position=:all)
    MacroExpansionError(nothing, ex, msg, position)
end

function Base.showerror(io::IO, exc::MacroExpansionError)
    print(io, "MacroExpansionError")
    ctx = exc.context
    if !isnothing(ctx)
        # Use `Expr` formatting to pretty print the macro name for now -
        # there's quite a lot of special cases. We could alternatively consider
        # calling sourcetext() though that won't work well if it's a
        # synthetically-generated macro name path.
        macname_str = string(Expr(
            :macrocall, est_to_expr(ctx.macrocall[1]), nothing))
        print(io, " while expanding ", macname_str,
              " in module ", syntax_module(ctx.macrocall))
    end
    print(io, ":\n")
    # TODO: Display niceties:
    # * Show the full provenance tree somehow, in addition to the primary
    #   source location we're showing here?
    # * What if the expression doesn't arise from a source file?
    # * How to deal with highlighting trivia? Could provide a token kind or
    #   child position within the raw tree? How to abstract this??
    src = sourceref(exc.ex)
    if src isa LineNumberNode
        highlight(io, src, note=exc.msg)
    else
        fb = first_byte(src)
        lb = last_byte(src)
        pos = exc.position
        byterange = pos == :all     ? (fb:lb)   :
            pos == :begin   ? (fb:fb-1) :
            pos == :end     ? (lb+1:lb) :
            error("Unknown position $pos")
        highlight(io, src.file[], byterange, note=exc.msg)
    end
    if !isnothing(exc.err)
        print(io, "\nCaused by:\n")
        showerror(io, exc.err)
    end
end

# Sentinel returned by `_eval_dot` when a name isn't a plain identifier/value or
# a qualified `.`-chain of them, so `eval_macro_name` can fall back to eval.
struct NotAName end

# Resolve a macro-name expression to its value *without* calling `eval`,
# mirroring the C `jl_eval_dot_expr` fast path that lets qualified names resolve
# even inside a generated-function ("pure") context. Handles identifiers,
# interpolated `Value` leaves (e.g. a `Module` spliced into the name, as in
# `$Mod.@mac`), and `.`-chains of them (`A.B.@mac`, `$Mod.Sub.@mac`); the
# leftmost identifier is looked up in `mod`. `getproperty` covers both module
# and non-module qualifiers, matching flisp. Returns `NotAName()` for anything
# that would require arbitrary evaluation.
function _eval_dot(world::UInt, mod, ex::SyntaxTree)
    k = kind(ex)
    if k === K"Value"
        return ex.value
    elseif k === K"Identifier"
        return _invoke_in_world(world, getproperty, mod, Symbol(ex.name_val))
    elseif k === K"." && numchildren(ex) == 2
        lhs = _eval_dot(world, mod, ex[1])
        lhs isa NotAName && return lhs
        rhs = ex[2]
        kind(rhs) === K"inert" && (rhs = rhs[1])
        kind(rhs) in KSet"Identifier Symbol" || return NotAName()
        return _invoke_in_world(world, getproperty, lhs, Symbol(rhs.name_val))
    else
        return NotAName()
    end
end

# If macroexpand(ex[1]) is an identifier or dot-expression, we can simply grab
# it from the correct module in ctx.world.  Otherwise, we need to eval arbitrary
# code (which, TODO: does not use the correct world age, and it isn't clear the
# language is meant to support this).
function eval_macro_name(ctx, mctx::MacroContext, st0::SyntaxTree)
    sc = st0.context::SyntaxContext
    mod = syntax_module(sc)
    st = expand_forms_1(ctx, st0)
    try
        if kind(st) === K"Value"
            st.value
        elseif kind(st) === K"Identifier"
            _invoke_in_world(ctx.world, getproperty,
                             syntax_module(st), Symbol(st.name_val))
        elseif kind(st) === K"." &&
                # TODO: correct mod?
                (ed = _eval_dot(ctx.world, mod, st); !(ed isa NotAName))
            ed
        else
            # The name isn't a plain identifier/value or a qualified `.`-chain
            # of them, so resolving it requires arbitrary evaluation. Inside a
            # generated-function ("pure") context flisp forbids exactly this (its
            # `jl_toplevel_eval` of the name hits the pure-callback guard once the
            # name is no longer an `a.b` fast path), so raise the same error here
            # rather than attempt a lowering that can only fail. At true top level
            # we evaluate, matching flisp.
            if ccall(:jl_is_in_pure_context, Int8, ()) != 0
                error("eval cannot be used in a generated function")
            end
            # `st` might contain a nontrivial mix of scopes so we can't just
            # `eval()` it, as it's already been partially lowered by this point.
            # Instead, we repeat the latter parts of `lower()` here.
            ctx2, st2 = expand_forms_2(st, ctx.world)
            ctx3, st3 = resolve_scopes(ctx2, st2)
            ctx4, st4 = convert_closures(ctx3, st3)
            _ctx5, st5 = linearize_ir(ctx4, st4)
            expr_form  = to_lowered_expr(st5)
            ccall(:jl_toplevel_eval, Any, (Any, Any), mod, expr_form)
        end
    catch err
        throw(MacroExpansionError(mctx, st, "Macro not found", :all, err))
    end
end

function _macrocall_expr_location(st::SyntaxTree)
    @jl_assert kind(st) === K"macrocall" st
    if kind(st[2]) === K"Value"
        loc = st[2].value
        if loc isa MacroSource
            loc
        elseif loc isa LineNumberNode
            # Some macros, e.g. @cmd, don't play nicely with file == nothing
            isnothing(loc.file) ? LineNumberNode(loc.line, :none) : loc
        elseif loc === nothing
            # A source-less macrocall (`Expr(:macrocall, name, nothing, ...)`)
            # gets `__source__ = LineNumberNode(0, nothing)`, exactly as flisp's
            # `jl_invoke_julia_macro`; macros detect the missing source by the
            # `nothing` file (e.g. Test's `@testset` backtrace scrubbing).
            LineNumberNode(0, nothing)
        else
            LineNumberNode(0, :none)
        end
    elseif kind(st[2]) === K"VERSION"
        loc = source_location(LineNumberNode, st)
        @static isdefinedglobal(Core, :MacroSource) ? Core.MacroSource(loc, st[2].value) : loc
    else
        LineNumberNode(0, :none)
    end
end

# Decide whether `macfunc` should be invoked with the new (`MacroContext`-based,
# `SyntaxTree` in and out) calling convention or the old
# (`(__source__, __module__, args...)`, `Expr` in and out) one.
#
# The discriminator is what our own `macro ... end` lowering stamps (see
# `expand_macro_def`): a new-style method declares its first positional
# parameter as `::MacroContext`. So we look up the method dispatch would select
# for a `MacroContext`-led call and check that parameter's type. A plain
# `hasmethod` on `Tuple{typeof(mctx), ...}` is not enough: any fully-variadic
# binding (e.g. a `ComposedFunction`, whose sole method is `(::ComposedFunction)
# (x...; kw...)`) matches every argument tuple, `MacroContext` included, and so
# would be misclassified as new-style even though it is an ordinary old-style
# macro returning an `Expr`.
# Returns the MethodInstance for a new-style invocation, or `nothing` if the
# binding is not a new-style macro (so the caller can reuse the lookup).
function new_style_macro_mi(macfunc, macro_args, world::UInt)
    mi = lookup_method_instance(macfunc, macro_args, world)
    mi === nothing && return nothing
    sig = Base.unwrap_unionall(mi.def.sig)
    sig isa DataType || return nothing
    params = sig.parameters
    # params[1] is `typeof(macfunc)`; params[2] is the first user-facing argument
    length(params) >= 2 || return nothing
    P = params[2]
    # `P isa Type` excludes a `Vararg` first parameter (the variadic catch-all
    # case above), which is not a `Type`.
    P isa Type || return nothing
    return P <: MacroContext ? mi : nothing
end

function expand_macro(ctx::MacroExpansionContext, st::SyntaxTree)
    @jl_assert kind(st) === K"macrocall" st
    numchildren(st) >= 2 || throw(LoweringError(
        st, "`macrocall` requires a macro name and source location"))
    sc_in = st.context::SyntaxContext
    macname = st[1]
    mctx = MacroContext(ctx.graph, st)
    macfunc = eval_macro_name(ctx, mctx, macname)
    raw_args = st[3:end]

    # `ctx.world === typemax(UInt)` is our sentinel for "latest world"
    macro_world = ctx.world === typemax(UInt) ? Base.get_world_counter() : ctx.world
    # The resolved MethodInstance doubles as the new-style test and as the
    # pre-resolved method for invocation below: a nested `require`/precompile
    # inside the macro can perturb method-table visibility at `ctx.world`, so
    # re-resolving after the body runs may fail. This matches flisp's single
    # lookup in `jl_invoke_julia_macro`.
    new_macro_args = Any[mctx, raw_args...]
    new_macro_mi = new_style_macro_mi(macfunc, new_macro_args, macro_world)

    if new_macro_mi !== nothing
        macro_args = new_macro_args
        macro_mi = new_macro_mi
        expanded = try
            _invoke_in_world(ctx.world, macfunc, macro_args...)
        catch exc
            newexc = exc isa MacroExpansionError ?
                MacroExpansionError(mctx, exc.ex, exc.msg, exc.position, exc.err) :
                MacroExpansionError(mctx, st, "Error expanding macro", :all, exc)
            rethrow(newexc)
        end
        st_out = if expanded isa SyntaxTree
            expanded._graph !== ctx.graph ? copy_ast(ctx, expanded) : expanded
        else
            expanded isa Expr && throw(LoweringError(
                st, "implicit expr->syntaxtree: may later be allowed, but is probably a mistake today"))
            expr_to_est(st._graph, expanded, st._id)
        end
    else
        macro_loc = _macrocall_expr_location(st)
        macro_args = Any[macro_loc, base_layer(ctx.syntax_context).mod]
        for arg in raw_args
            @jl_assert kind(arg) !== K"VERSION" arg # handled in EST conversion
            push!(macro_args, est_to_expr(arg))
        end
        macro_mi = lookup_method_instance(macfunc, macro_args, macro_world)
        st_out = try
            _invoke_in_world(ctx.world, macfunc, macro_args...)
        catch exc
            if exc isa MethodError && exc.f === macfunc && !isempty(
                methods_in_world(macfunc, Tuple{typeof(mctx), Vararg{Any}}, ctx.world, st))
                # If the macro has at least some methods implemented in the
                # new style, assume the user meant to call one of those
                # rather than any old-style macro methods which might exist
                exc = MethodError(macfunc, (mctx, raw_args...,), ctx.world)
            end
            rethrow(MacroExpansionError(mctx, st, "Error expanding macro", :all, exc))
        end
        macro_lnn = macro_loc isa MacroSource ? macro_loc.lno : macro_loc
        st_out = expr_to_est(st._graph, st_out, macro_lnn)
    end
    # Module scope for the returned AST is the module where this particular
    # method was defined (may be different from `parentmodule(macfunc)`)
    mod_for_ast = macro_mi !== nothing ? macro_mi.def.module : parentmodule(macfunc)
    sc2 = SyntaxContext(
        ScopeLayer(mod_for_ast, sc_in.layer), st,
        (new_macro_mi !== nothing ? JL_NEW_SYNTAX_VERSION : JL_OLD_SYNTAX_VERSION), false)
    st_out2 = apply_expansion_layer(ctx, st_out, sc2, true, 0, 0)
    st_res = !ctx.recursive ? st_out2 : expand_forms_1(ctx, st_out2)
    mark_expansion_root_method!(st_res)
    st_res
end

# flisp resolves an unescaped method-def name that is the *root* of a macro
# expansion as a plain global of the macro's home module, unlike a nested (e.g.
# block- or quote-wrapped) def, which stays hygienically renamed.  Mark the root
# def name so scope analysis can reproduce that rule (see `_find_scope_decls!`).
function mark_expansion_root_method!(st)
    k = kind(st)
    if k === K"function" && numchildren(st) == 1
        name = st[1] # `function f end` forward declaration
    elseif k === K"function" || (k === K"=" && is_eventually_call(st[1]))
        sig = st[1]
        while kind(sig) === K"where"; sig = sig[1]; end
        kind(sig) === K"::" && numchildren(sig) == 2 && (sig = sig[1])
        kind(sig) === K"call" || return
        name = sig[1]
        kind(name) === K"curly" && (name = name[1])
    else
        return
    end
    kind(name) === K"Identifier" && !hasattr(name, :mod) &&
        setmeta!(name, :expansion_root_method, true)
    nothing
end

function known_layer(ctx, sl::Union{Nothing, ScopeLayer})
    isnothing(sl) && return false
    get!(ctx.known_layers, sl) do
        known_layer(ctx, sl.escaped)
    end
end

"""
When a macro expands, we add a fresh layer to all new syntax in the expansion.
Any syntax that doesn't share a base layer with the top-level thunk is
considered "new".  This is similar to racket's flip-scope operation, but
simpler and less powerful (we lose any layer we overwrite, but we gain the
invariant that all layers have the same root after every expansion, so
`escape` is well-defined).

Implementation notes:

- `escape` can never be resolved to a layer inside a macrocall, since we must
  expand to know whether (old) more escapes will surround it or (new) the macro
  moves the escape to another layer.

- `escape` nodes coming in usually have no layer (old expansion).  New
  expansions can't create escapes, but can pass an argument containing `escape`
  through, and arguments must have full context.  Thus, if we see `escape` with
  any context, we know the layer is uniform, and is the layer we want to escape
  from, so we remove inner context. (if there's an an old macro requiring
  caller-side `esc(arg)`, the new macro must also bump `esc(arg)`'s layer.)

- We could try some shortcuts in module/toplevel, but note that macrocall/quote
  need full context (a macro may extract an arbitrary child), and even when
  `done`, module/toplevel may contain syntax with arbitrary layers that we must
  clean up now (later, we lose the base layer used to detect new syntax)
"""
function apply_expansion_layer(ctx, st::SyntaxTree, sc_in::SyntaxContext, done,
                               qdepth, sqdepth)
    @jl_assert known_layer(ctx, base_layer(sc_in)) st
    sc0 = get(st, :context, nothing)::Union{Nothing, SyntaxContext}
    sc = (isnothing(sc0) || !known_layer(ctx, sc0.layer)) ? sc_in : sc0
    k = kind(st)
    absorb_esc = done && qdepth == 0 && sqdepth == 0
    out = if is_leaf(st) || numchildren(st) == 0
        setattr(st, :context, sc)
    elseif k === K"escape" && absorb_esc
        if numchildren(st) !== 1
            throw(LoweringError(st, "`escape` requires one argument"))
        elseif is_base_layer(sc)
            throw(LoweringError(st, "`escape` node in outer context"))
        elseif !is_flisp_compat(sc)
            throw(LoweringError(st, "new macros should not use `escape`"))
        end
        st1 = isnothing(sc0) ? st[1] : remove_context(st[1])
        apply_expansion_layer(
            ctx, st1, escape_layer(sc, false), true, qdepth, sqdepth)
    elseif k === K"hygienic-scope" && absorb_esc
        if !(2 <= numchildren(st) <= 3)
            throw(LoweringError(st, "`hygienic-scope` requires 2-3 children"))
        elseif kind(st[2]) !== K"Value" || !(st[2].value isa Module)
            throw(LoweringError(st, "`hygienic-scope` arg 2: expected Module"))
        elseif !is_flisp_compat(sc)
            throw(LoweringError(st, "new macros should not use `hygienic-scope`"))
        end
        new_sl = ScopeLayer(st[2].value::Module, sc.layer)
        st1 = isnothing(sc0) ? st[1] : remove_context(st[1])
        sc2 = SyntaxContext(new_sl, sc.unexpanded, sc.version, sc.internal)
        apply_expansion_layer(ctx, st1, sc2, true, qdepth, sqdepth)
    else
        done2 = done && !(k in KSet"macrocall inert syntaxinert")
        qdepth2 = qdepth + (k === K"quote" ? 1 : k === K"$" ? -1 : 0)
        sqdepth2 = sqdepth + (k === K"syntaxquote" ? 1 : k === K"syntaxunquote" ? -1 : 0)
        out = mapchildren(c->apply_expansion_layer(
            ctx, c, sc_in, done2, qdepth2, sqdepth2), ctx, st)
        setattr!(out, :context, sc)
    end
    out
end

"""
Expands macros and quote/interpolation forms.
"""
function expand_forms_1(ctx::MacroExpansionContext, st::SyntaxTree)
    k = kind(st)
    if is_leaf(st)
        st
    elseif k === K"macrocall"
        expand_macro(ctx, st)
    elseif (k === K"do" && numchildren(st) == 2 && kind(st[1]) === K"macrocall" &&
        kind(st[2]) === K"->")
        mac_ex = @ast ctx st [
            K"macrocall"
            st[1][1] # mac name
            st[1][2] # loc
            st[2]    # do-lambda
            children(st[1])[3:end]...
        ]
        expand_macro(ctx, mac_ex)
    elseif k in KSet"inert syntaxinert toplevel module"
        st
    elseif k === K"quote"
        if numchildren(st) !== 1
            throw(LoweringError(st, "`quote` requires one argument"))
        end
        expand_forms_1(ctx, expand_quote(ctx, st[1]))
    elseif k === K"syntaxquote"
        if numchildren(st) !== 1
            throw(LoweringError(st, "`syntaxquote` requires one argument"))
        end
        expand_forms_1(ctx, expand_syntaxquote(ctx, st[1]))
    elseif k === K"escape" || k === K"hygienic-scope"
        expand_forms_1(
            ctx, apply_expansion_layer(
                ctx, st, st.context::SyntaxContext, true, 0, 0))
    else
        mapchildren(c->expand_forms_1(ctx, c), ctx, st)
    end
end

function ensure_macro_attributes!(graph)
    g2 = ensure_attributes!(
        graph;
        var_id=IdTag,
        meta=CompileHints)
    DEBUG ? ensure_attributes!(g2; jl_source=LineNumberNode) : g2
end

function assert_expandable(st, l=base_layer(st.context::SyntaxContext))
    @jl_assert hasattr(st, :context) (st, "expected syntax context")
    @jl_assert base_layer(st.context::SyntaxContext) == l (st, "expected consistent layer")
    for c in children(st)
        assert_expandable(c, l)
    end
end

"""
Give unescaped `@label`/`@goto` names their own hygienic identity per macro
expansion, mirroring flisp's `rename-symbolic-labels` pass (`src/macroexpand.scm`).

`@label`/`@goto` names are ordinary literal strings that would otherwise be
compared verbatim when control flow is linearized, so two expansions of a
label-emitting macro landing in one lambda would collide (and, conversely, a
`@goto` in one expansion would wrongly resolve to a same-named `@label` in
another). flisp avoids this by gensym-renaming each label per macro
`hygienic-scope`, memoized so a label and its matching goto in the same
expansion stay connected.

We get the same effect for free from the layer system: every macro expansion
allocates a fresh `ScopeLayer`, and `apply_expansion_layer` already resolves
`esc` by popping a name to its caller's layer.  So we key the rename on
`(layer, name)`: labels sharing a layer resolve to each other, distinct
expansions get distinct names, and base-layer names (user-written labels, or
labels escaped all the way to the call site) keep their literal spelling and
stay reachable by an unescaped `@goto` at that site.

Renamed labels use flisp's `#N#name` format with session-global counter
semantics (flisp's `named-gensy` draws from the session-wide `*gensy-counter*`).
A per-expansion counter would make the first renamed label deterministically
`#1#name`, so user code literally spelling `var"#1#lbl"` would collide with (or
silently bind to) a macro's renamed internal label; with the global counter such
collisions are as improbable as under flisp. The renamed names are erased at
linearization, so the global counter has no reproducibility cost for lowered
code.
"""
const _label_rename_counter = Threads.Atomic{Int}(0)

function rename_symbolic_labels!(st::SyntaxTree, relabels)
    k = kind(st)
    if is_leaf(st) || k in KSet"inert syntaxinert"
        return st
    elseif (k === K"symboliclabel" || k === K"symbolicgoto" ||
            k === K"oldsymbolicgoto") && numchildren(st) == 1 &&
            kind(st[1]) === K"Identifier"
        name_node = st[1]
        sc = get(name_node, :context, nothing)::Union{Nothing, SyntaxContext}
        # Only rename names introduced by a macro expansion (non-base layer);
        # base-layer names are the flisp `parent-scope` null case (no rename).
        (isnothing(sc) || sc.layer.escaped === nothing) && return st
        name = name_node.name_val
        newname = get!(relabels, (sc.layer, name)) do
            n = Threads.atomic_add!(_label_rename_counter, 1) + 1
            string("#", n, "#", name)
        end
        newname == name && return st
        return mknode(st, SyntaxList(setattr(name_node, :name_val, newname)))
    else
        return mapchildren(
            c->rename_symbolic_labels!(c, relabels), st._graph, st)
    end
end

function rename_symbolic_labels!(st::SyntaxTree)
    rename_symbolic_labels!(st, Dict{Tuple{ScopeLayer, String}, String}())
end

@fzone "JL: macroexpand" function expand_forms_1(
    st::SyntaxTree, world::UInt, recursive::Bool)

    graph = ensure_macro_attributes!(copy_attrs(syntax_graph(st)))
    st = reparent(graph, st)
    DEBUG && assert_expandable(st)
    ctx = MacroExpansionContext(st, world, recursive)
    st_out = expand_forms_1(ctx, st)
    st_out = rename_symbolic_labels!(st_out)
    return st_out
end
