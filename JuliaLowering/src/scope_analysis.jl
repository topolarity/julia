# Lowering pass 3: scope and variable analysis

"""
Key to use when transforming names into bindings
"""
struct NameKey
    name::String
    layer::ScopeLayer
end

function NameKey(ex::SyntaxTree)
    @jl_assert kind(ex) === K"Identifier" ex
    NameKey(ex.name_val, (ex.context::SyntaxContext).layer)
end

# True if `anc` is a strict ancestor of `layer` on the `escaped` chain, i.e.
# `layer` was produced by a macro expansion nested (via `esc`) inside `anc`.
function is_strict_ancestor_layer(anc::ScopeLayer, layer::ScopeLayer)
    l = layer.escaped
    while l !== nothing
        l === anc && return true
        l = l.escaped
    end
    return false
end

struct ScopeInfo
    # index into ctx.scopes
    id::ScopeId
    # 0 if top-level thunk
    parent_id::ScopeId
    # Own ID if lambda, else some parent ID
    lambda_id::ScopeId
    # Tree introducing this scope
    node_id::NodeId
    # True in the top-level scope, and any neutral scope nested within it not
    # protected by a hard scope.  Becomes soft if `ctx.enable_soft_scopes`.
    is_permeable::Bool
    # True for K"method_defs" and its non-lambda children where all new locals
    # should participate in standard scope resolution, but then be associated
    # with the top-level thunk by the end of this pass.
    is_lifted::Bool
    binding_assignments::Dict{IdTag, NodeId}
    assignments::Dict{NameKey, NodeId}
    # Map from variable names to binding IDs for resolution.  Includes all
    # locals, args, sparams, and explicit globals belonging to this scope.
    # Variables captured from an outer scope are not included.  The top-level
    # scope also contains all globals for resolution to fall back to.
    vars::Dict{NameKey,IdTag}
    # flisp-compat read-only aliases for cross-layer argument name references
    # (see `register_arg_name_aliases!` and `register_kwarg_aliases!`): consulted by
    # `resolve_name` when `vars` misses, but invisible to assignment targets and
    # explicit declarations, which get fresh hygienic locals as under flisp.
    arg_aliases::Dict{NameKey,IdTag}
    # flisp-compat: arg/sparam bindings whose name is shadowed by a `global`
    # declaration in the same lambda.  `vars` maps the name to the shadowing
    # global for body resolution; this keeps the original arg/sparam binding so
    # the lambda's declaring parameter list still binds its slot (see
    # `resolve_lambda_params` and `explicit_declare_in_scope!`).
    shadowed_params::Dict{NameKey,IdTag}
    # See `LambdaBindings`. Nothing if not a lambda scope.  This is the final
    # collecting place for locals going in to closure conversion.
    locals_capt::Union{Nothing, Dict{IdTag,Bool}}
end

function ScopeInfo(ctx, parent_id, ex::SyntaxTree)
    id = length(ctx.scopes) + 1
    if parent_id == 0
        @jl_assert kind(ex) === K"lambda" ex
        lambda_id = id
        is_permeable = ex.is_toplevel_thunk
        is_lifted = false
    else
        parent = ctx.scopes[parent_id]
        lambda_id = kind(ex) === K"lambda" ? id : parent.lambda_id
        is_permeable = (kind(ex) === K"scope_block" &&
            ex.scope_type === :neutral && parent_id !== 0 && parent.is_permeable)
        is_lifted = kind(ex) === K"method_defs" ||
            (kind(ex) !== K"lambda" && parent.is_lifted)
    end
    s = ScopeInfo(
        id, parent_id, lambda_id, ex._id, is_permeable, is_lifted,
        Dict{IdTag, NodeId}(), Dict{NameKey, NodeId}(), Dict{NameKey,IdTag}(),
        Dict{NameKey,IdTag}(), Dict{NameKey,IdTag}(),
        kind(ex) === K"lambda" ? Dict{IdTag,Bool}() : nothing)
    push!(ctx.scopes, s)
    return s
end

struct ScopeResolutionContext{Attrs} <: AbstractLoweringContext
    graph::SyntaxGraph{Attrs}
    layer::ScopeLayer
    bindings::Bindings
    # Purely for display and deterministic ordering of scope layers
    layer_ids::Dict{ScopeLayer, Int}
    # Every lexical scope, indexed by ScopeId
    scopes::Vector{ScopeInfo}
    # Current stack of scopes to look for names in, innermost scope last
    scope_stack::Vector{ScopeId}
    # Usually, globals in the top scope are ignored.  This is a subset that may
    # be assigned to without the `global` keyword in soft scopes due to being
    # assigned to at top level, or passing the defined-and-owned-global check.
    soft_assignable_globals::Set{NameKey}
    # Every static parameter corresponds to some typevar (top-level local)
    # required to create this method
    sp_typevars::Dict{IdTag, IdTag}
    # Typevars referenced in each typevar's bounds.  Closures capturing a static
    # parameter must also capture the sparams of its typevar's dependencies
    tv_deps::Dict{IdTag, Vector{IdTag}}
    enable_soft_scopes::Bool
    world::UInt
end

function contains_softscope_marker(ex)
    kind(ex) == K"softscope"  && return true
    needs_resolution(ex) && for c in children(ex)
        contains_softscope_marker(c) && return true
    end
    return false
end

top_scope(ctx) = ctx.scopes[1]
is_top_scope(scope::ScopeInfo) = scope.parent_id === 0
enclosing_lambda(ctx, scope::ScopeInfo) = ctx.scopes[scope.lambda_id]
parent(ctx, scope::ScopeInfo) = is_top_scope(scope) ? nothing :
    ctx.scopes[scope.parent_id]

_var_str(v) = v === :local ? "local variable" :
    v === :global ? "global variable" :
    v === :argument ? "argument" :
    v === :destructured_arg ? "destructured argument" :
    v === :typevar ? "typevar" :
    v === :static_parameter ? "static parameter" : "unknown"

# Declare `ex` in `scope`, unless a binding already exists with the same name in
# scope, or anywhere.  Throw an error if a name conflict occurs.  The rules
# for conflict: declaring a local (or global) twice with the same name is a
# no-op, but doing so with an argument or static parameter is an error.  A
# variable usually can't be two things in one scope, but flisp has quirks.
function explicit_declare_in_scope!(ctx, scope::ScopeInfo, ex, new_k::Symbol)
    if kind(ex) === K"BindingId"
        bid = ex.var_id
        b = get_binding(ctx, bid)
        @jl_assert b.kind === new_k ex
        @jl_assert b.lambda_id == 0 (ex, "cannot declare a BindingId in multiple scopes")
        add_lambda_local!(ctx, scope, b)
        return bid
    elseif kind(ex) === K"Placeholder"
        return nothing
    end
    bid = get(scope.vars, NameKey(ex), nothing)
    old_k = isnothing(bid) ? nothing : get_binding(ctx, bid).kind
    result_bid = if isnothing(old_k)
        if new_k === :argument
            declare_in_scope!(ctx, scope, ex, :argument;
                              is_nospecialize=getmeta(ex, :nospecialize, false))
        elseif new_k === :global &&
                (ip = find_identity_param(ctx, scope, ex); !isnothing(ip))
            # An identity-mapped param spelled as the same raw symbol in flisp
            # (see below) is shadowed even though its exact key differs.
            shadow_param_with_global!(ctx, scope, ex, ip...)
        else
            real_k = new_k === :destructured_arg ? :local : new_k
            declare_in_scope!(ctx, scope, ex, real_k)
        end
    elseif old_k === new_k
        if new_k === :global || new_k === :local
            bid
        else
            throw(LoweringError(ex, "function $(_var_str(new_k)) name not unique"))
        end
    # flisp compat: a `global x` declaration written alongside an argument or
    # static parameter also named `x` shadows that arg/sparam for the *whole*
    # lambda body (see test/scopes.jl "globals may overlap args or sparams").
    # Re-declare `x` as a global so every body reference and assignment resolves
    # to the module global, but remember the arg/sparam binding so the lambda's
    # own parameter list still binds its (now dead) slot in `resolve_lambda_params`.
    # Only shadow when flisp would see the declaration and the parameter as the
    # same raw symbol: they share a syntax context (both written in the same
    # expansion), or the parameter is identity-mapped (a kwarg name or esc'd
    # named-def argument, which flisp leaves raw, so a colliding raw `global`
    # shadows it too).  An unhygienic old-macro `global` relayered onto a
    # caller's anonymous-lambda arg or sparam (`relayer_global_if_unhygienic`)
    # matches neither, and still errors as a rescoping conflict.
    elseif new_k === :global && old_k in (:argument, :static_parameter) &&
            ((ex.context::SyntaxContext) === (binding_ex(ctx, bid).context::SyntaxContext) ||
             get_binding(ctx, bid).is_flisp_identity)
        shadow_param_with_global!(ctx, scope, ex, NameKey(ex), bid)
    else
        throw(LoweringError(ex, """
        $(_var_str(new_k)) name `$(NameKey(ex).name)` conflicts with an \
        existing $(_var_str(old_k)) from the same scope"""))
    end
    register_kwarg_aliases!(ctx, scope, ex, result_bid)
    register_arg_name_aliases!(ctx, scope, ex, result_bid)
    return result_bid
end

# Find an identity-mapped argument or static parameter in `scope` that flisp
# would spell as the same raw symbol as the `global` declaration `ex`: same
# name, on a related layer (`===` or ancestor in either direction; unrelated
# layers are gensym-renamed by flisp and cannot collide).  This catches e.g. a
# relayered old-macro `global x` whose key differs from a bare kwarg `x` of the
# same expansion.  Returns `(key, binding_id)` or `nothing`.
function find_identity_param(ctx, scope::ScopeInfo, ex)
    nk = NameKey(ex)
    best_key = nothing
    best_bid = 0
    for (k, bid) in scope.vars
        k.name == nk.name || continue
        k.layer === nk.layer || is_strict_ancestor_layer(k.layer, nk.layer) ||
            is_strict_ancestor_layer(nk.layer, k.layer) || continue
        b = get_binding(ctx, bid)
        b.is_flisp_identity && b.kind in (:argument, :static_parameter) || continue
        # Deterministic pick among (pathological) multiple matches
        if isnothing(best_key) ||
            get(ctx.layer_ids, k.layer, typemax(Int)) <
            get(ctx.layer_ids, best_key.layer, typemax(Int))
            best_key = k
            best_bid = bid
        end
    end
    isnothing(best_key) ? nothing : (best_key, best_bid)
end

# Apply the whole-scope global shadow: declare `ex` as a global, redirect the
# shadowed param's name (and any `arg_aliases` still pointing at it) to the
# global so every body reference resolves there, and record the param binding
# for `resolve_lambda_params`.
function shadow_param_with_global!(ctx, scope::ScopeInfo, ex, param_key::NameKey, param_bid)
    scope.shadowed_params[param_key] = param_bid
    gid = declare_in_scope!(ctx, scope, ex, :global)
    scope.vars[param_key] = gid
    for (k, v) in scope.arg_aliases
        v == param_bid && (scope.arg_aliases[k] = gid)
    end
    return gid
end

# flisp compat, the forward direction: an old-style macro may escape an
# argument *name* (`esc(:x)`) of a named method definition while the body
# refers to the same symbol bare.  flisp identity-maps escaped argument names
# in the expansion environment (macroexpand.scm `keywords-introduced-by` via
# `safe-llist-keyword-args`), so bare references resolve to the argument; here
# the two occurrences carry different layers, so register a read-only alias at
# exactly the enclosing lambda's layer.  Desugaring tags the argument names of
# named definitions `:is_method_arg_name` -- positional args, kwargs, varargs
# and destructured (tuple) components, the latter reaching here as
# `:destructured_arg` locals rather than lambda args -- while anonymous
# functions, `->`/`do`/generator lambdas, macro definitions and the self name
# of a callable-object definition stay untagged, matching flisp's closed
# pattern list.  Deeper nested expansions keep their hygiene, and
# assignments/declarations don't see the alias (see `arg_aliases`).
function register_arg_name_aliases!(ctx, scope::ScopeInfo, ex, bid)
    (isnothing(bid) || kind(ex) !== K"Identifier") && return
    getmeta(ex, :is_method_arg_name, false) || return
    sc = ex.context::SyntaxContext
    is_flisp_compat(sc) || return
    lam_node = SyntaxTree(ctx.graph, enclosing_lambda(ctx, scope).node_id)
    lam_layer = (lam_node.context::SyntaxContext).layer
    if is_strict_ancestor_layer(sc.layer, lam_layer)
        get!(scope.arg_aliases, NameKey(ex.name_val, lam_layer), bid)
        # An esc'd argument name of a named def is identity-mapped in flisp:
        # references to it are raw-symbol shadowable (see `resolve_name`).
        get_binding(ctx, bid).is_flisp_identity = true
    end
    return
end

# flisp compat, the reverse of the escaped-argument-name aliases registered in
# `register_arg_name_aliases!`: an old-style macro emits a keyword-argument *name* bare (its
# own layer) while esc'd defaults or the body reference it from an ancestor
# (caller) layer.  flisp exempts keyword-arg names from hygiene renaming
# (macroexpand.scm `safe-llist-keyword-args`), so those references bind to the
# kwarg.  Desugaring tags kwarg-derived binding sites `:is_keyword_arg`; register
# a read-only alias at each ancestor layer of the kwarg's own layer pointing back
# to its binding.  As with the forward direction the alias is read-only, so a
# bare name that is assigned or explicitly declared still gets a fresh hygienic
# local (matching flisp's gensym renaming), and unrelated nested expansions,
# whose layers are not on this ancestry, keep their hygiene.
function register_kwarg_aliases!(ctx, scope::ScopeInfo, ex, bid)
    (isnothing(bid) || kind(ex) !== K"Identifier") && return
    getmeta(ex, :is_keyword_arg, false) || return
    sc = ex.context::SyntaxContext
    is_flisp_compat(sc) || return
    # A keyword-arg name (bare or esc'd) is identity-mapped in flisp:
    # references to it are raw-symbol shadowable (see `resolve_name`).
    get_binding(ctx, bid).is_flisp_identity = true
    aliases = scope.arg_aliases
    l = sc.layer.escaped
    while l !== nothing
        get!(aliases, NameKey(ex.name_val, l), bid)
        l = l.escaped
    end
    return
end

# globals are added to both `scope` and the top scope (mainly so we can get the
# same binding for many unrelated global references).
function declare_in_scope!(ctx, scope::ScopeInfo, ex, bk::Symbol; kws...)
    nk = NameKey(ex)
    if bk === :global
        mod = syntax_module(ex)
        declaration_scope = top_scope(ctx)
    else
        declaration_scope = scope
        mod = hasattr(ex, :mod) ?
            throw(LoweringError(ex, "cannot use GlobalRef as local identifier")) : nothing
    end
    is_internal = (ex.context::SyntaxContext).internal ||
        getmeta(ex, :is_internal, false)::Bool
    b = _new_binding(ctx, ex, nk.name, bk; mod, is_internal, kws...)
    declaration_scope.vars[nk] = b.id
    scope.vars[nk] = b.id
    add_lambda_local!(ctx, scope, b)
    return b.id
end

function add_lambda_local!(ctx, scope::ScopeInfo, b)
    if b.kind === :global || b.is_ssa
        return
    end
    lam = scope.is_lifted ? top_scope(ctx) : enclosing_lambda(ctx, scope)
    b.kind == :typevar && @jl_assert scope.is_lifted binding_ex(ctx, b)
    @jl_assert !haskey(lam.locals_capt, b.id) (
        binding_ex(ctx, b), "adding lambda local twice")
    lam.locals_capt[b.id] = false
    b.lambda_id = lam.id
    nothing
end

function ensure_captured!(ctx, scope::ScopeInfo, b)
    if b.kind === :global || b.kind === :typevar || b.is_ssa
        return
    end
    lam = enclosing_lambda(ctx, scope)
    if !haskey(lam.locals_capt, b.id)
        # assert is opaque closure, or b not static_parameter
        b.is_captured = true
        lam.locals_capt[b.id] = true
        s2 = parent(ctx, lam)
        @jl_assert !isnothing(s2) (
            binding_ex(ctx, b),
            "tried to capture local before declaration in any parent")
        ensure_captured!(ctx, s2, b)
    end
    nothing
end

function needs_resolution(ex)
    kind(ex) === K"Identifier" ||
        !is_leaf(ex) && !is_quoted(ex) && !(kind(ex) in KSet"toplevel module")
end

# An `arg_aliases` entry or an `is_flisp_identity` binding stands for flisp's
# *identity mapping* of the name: in flisp the reference and the binder are
# left as the raw symbol, so a reference is subject to ordinary lexical
# shadowing by any same-named binder that flisp also leaves as the raw symbol
# between the reference and the identity-mapped one -- e.g. an esc'd
# `->`/`do`/generator argument or an esc'd `let` binding of the same name,
# which carries a different scope layer here and therefore cannot shadow by
# exact (name, layer) key.  A binder spells the same raw symbol exactly when
# its layer is the reference's layer or an ancestor of it (escapes unwrap to
# the plain symbol; unrelated nested expansions gensym-rename instead), so:
# resolve to the nearest lexically-enclosing same-*named* non-global binding
# on the reference's layer ancestry, from the innermost scope out to `outer_i`
# (the scope holding the identity-mapped binding).  Binders on the reference's
# own layer only matter within `outer_i` itself (an inner one would have
# resolved by exact key already), where the identity-mapped binding acts as
# its own fallback.
function _nearest_shadowing_binder(ctx, nk::NameKey, outer_i::Int)
    # References on a base layer have no ancestor layers: nothing can shadow.
    isnothing(nk.layer.escaped) && return nothing
    stack = ctx.scope_stack
    for i in lastindex(stack):-1:outer_i
        scope = ctx.scopes[stack[i]]
        best_key = nothing
        best_bid = 0
        for (k, bid) in scope.vars
            k.name == nk.name || continue
            k.layer === nk.layer || is_strict_ancestor_layer(k.layer, nk.layer) ||
                continue
            get_binding(ctx, bid).kind === :global && continue
            # Deterministic pick among (pathological) multiple same-named
            # bindings from different layers in one scope.
            if isnothing(best_key) ||
                get(ctx.layer_ids, k.layer, typemax(Int)) <
                get(ctx.layer_ids, best_key.layer, typemax(Int))
                best_key = k
                best_bid = bid
            end
        end
        isnothing(best_key) || return get_binding(ctx, best_bid)
    end
    return nothing
end

# `include_arg_aliases=false` is used for assignment-target resolution, where
# an `arg_aliases` entry must be invisible so that assigning a bare name
# co-spelled with an escaped parameter introduces a fresh hygienic local
# (matching flisp's gensym-renaming) instead of mutating the parameter.
# One intentional exception: a target escaped OUT of a nested expansion
# (`is_escaped_binding_target`) skips declaration registration entirely and
# resolves here with aliases visible, like a reference — flisp resolves such
# a target in the parent expansion's env exactly as it would a reference.
function resolve_name(ctx, ex; exclude_toplevel_globals=false,
                      include_arg_aliases=true)
    # TODO: probably want to cache these lookups
    nk = NameKey(ex)
    stack = ctx.scope_stack
    for i in lastindex(stack):-1:firstindex(stack)
        sid = stack[i]
        scope = ctx.scopes[sid]
        bid = get(scope.vars, nk, nothing)
        if include_arg_aliases
            if isnothing(bid)
                bid = get(scope.arg_aliases, nk, nothing)
                if !isnothing(bid)
                    # flisp raw-symbol lexical shadowing: an intervening
                    # same-named binder on the reference's layer ancestry wins
                    # over the alias; see `_nearest_shadowing_binder`.
                    b2 = _nearest_shadowing_binder(ctx, nk, i)
                    isnothing(b2) || return b2
                end
            elseif get_binding(ctx, bid).is_flisp_identity
                # Same, for a direct hit on an identity-mapped binding (e.g. a
                # bare keyword-arg name): flisp leaves the binder as the raw
                # symbol too, so intervening esc'd binders shadow it.
                b2 = _nearest_shadowing_binder(ctx, nk, i)
                isnothing(b2) || return b2
            end
        end
        isnothing(bid) && continue
        b = get_binding(ctx, bid)
        if b.kind === :typevar
            # only visible to lifted scopes in the same lambda (we should only
            # hit this when we filter sparams with `used_typevars`)
            s0 = ctx.scopes[ctx.scope_stack[end]]
            s0.is_lifted && ctx.scopes[sid].lambda_id == s0.lambda_id || continue
        end
        if !exclude_toplevel_globals || sid !== top_scope(ctx).id || b.kind !== :global
            return b
        end
    end
    return nothing
end

# Collect typevar bindings referenced in `ex` (a resolved typevar bound)
function _typevar_refs!(out, ctx, ex)
    k = kind(ex)
    if k == K"BindingId"
        b = get_binding(ctx, ex)
        b.kind === :typevar && !(b.id in out) && push!(out, b.id)
    elseif !is_leaf(ex) && needs_resolution(ex)
        foreach(e->_typevar_refs!(out, ctx, e), children(ex))
    end
end

# Resolve an identifier as a global reference, ignoring any co-named local.
# Used for positions that are global-by-construction, e.g. the bare-symbol
# `@cfunction` callee: flisp resolves it in global scope at compile time,
# invisible to local shadowing (matching `@cfunction`'s documented semantics).
function resolve_as_global(ctx, ex)
    @jl_assert kind(ex) === K"Identifier" ex
    if (mod = get(ex, :mod, nothing); !isnothing(mod))
        return new_global_binding(ctx, ex, ex.name_val, mod)
    end
    ts = top_scope(ctx)
    bid = get(ts.vars, NameKey(ex), nothing)
    if isnothing(bid) || get_binding(ctx, bid).kind !== :global
        bid = declare_in_scope!(ctx, ts, ex, :global)
    end
    newleaf(ctx, ex, K"BindingId", bid)
end

# The self argument that `@__FUNCTION__` (K"thisfunction") resolves to: the
# enclosing lambda's first argument, unless another argument is explicitly marked
# as the logical self (e.g. the keyword-body method, where the original generic
# function is passed as a positional arg -- see `keywords_method_def_expr`).
function thisfunction_self_arg(ctx, ex, scope::ScopeInfo)
    lam = SyntaxTree(ex._graph, enclosing_lambda(ctx, scope).node_id)
    self_arg = lam[1][1]
    for a in children(lam[1])
        getmeta(a, :thisfunction_original, false) && (self_arg = a)
    end
    return self_arg
end

# flisp-compat: flisp names a method's implicit self argument with the literal,
# unhygienic symbol `#self#` (julia-syntax.scm), so user source that writes
# `var"#self#"` resolves to the enclosing method's own function object -- a
# long-standing idiom (predating `@__FUNCTION__`) for getting the enclosing
# function without hardcoding its name.  JuliaLowering mints the implicit self as
# a hygienic internal gensym, invisible to such a reference, so we recover the
# leak here: an otherwise-unresolved `#self#` written in flisp-compat source
# resolves to the same self as `@__FUNCTION__`, but only where flisp exposed one
# -- i.e. where the enclosing lambda's self is the implicit `#self#` (plain
# methods, closures, do-blocks, anonymous functions) or the keyword-body's
# original-function arg.  When the self is explicitly named (e.g. a callable
# `(self::T)(...)` method), flisp created no `#self#` binding and errored, so we
# leave the reference unresolved to match.
function is_self_hash_leak(ctx, ex, scope::Union{Nothing,ScopeInfo})
    (scope isa ScopeInfo && kind(ex) === K"Identifier" &&
        ex.name_val == "#self#" && is_flisp_compat(ex)) || return false
    is_top_scope(enclosing_lambda(ctx, scope)) && return false
    self_arg = thisfunction_self_arg(ctx, ex, scope)
    # Only expose the leak where flisp did: an implicit `#self#`, or the
    # keyword-body's redirected original-function arg.
    return (kind(self_arg) === K"Identifier" && self_arg.name_val == "#self#") ||
        getmeta(self_arg, :thisfunction_original, false)
end

function _record_layer!(ctx, ex)
    !hasattr(ex, :context) && return
    sl = (ex.context::SyntaxContext).layer
    get!(ctx.layer_ids, sl, length(ctx.layer_ids)+1)
end

# flisp-compat: true when a binding form's target name was `esc`ed out of a
# more deeply nested expansion than the one being resolved, i.e. the target's
# layer is a strict ancestor of the form's own layer.  flisp's expansion-env
# scan (`find-assigned-vars-in-expansion` and friends) resumes at `escape`s
# but then sees only the escaped fragment -- here a bare name -- so such a
# target is never counted as introduced by the enclosing expansion; it
# resolves there like any other reference: to whatever the enclosing
# expansion binds under that name, or else a plain global of the enclosing
# macro's home module (the target layer's module).
function is_escaped_binding_target(ctx, form, target)
    kind(target) === K"Identifier" && !hasattr(target, :mod) || return false
    sc = target.context::SyntaxContext
    return is_flisp_compat(sc) && !is_base_layer(sc) && sc.layer !== ctx.layer &&
        hasattr(form, :context) &&
        is_strict_ancestor_layer(sc.layer, (form.context::SyntaxContext).layer)
end

function _find_scope_decls!(ctx, scope, ex)
    k = kind(ex)
    _record_layer!(ctx, ex)
    if k === K"local" && kind(ex[1]) === K"Identifier"
        var_k = getmeta(ex, :is_destructured_arg, false) ?
            :destructured_arg : :local
        explicit_declare_in_scope!(ctx, scope, ex[1], var_k)
    elseif k === K"global" && kind(ex[1]) === K"Identifier"
        explicit_declare_in_scope!(ctx, scope, ex[1], :global)
    elseif k === K"relayered_global"
        # `(relayered_global orig relayered)`: an unhygienic old-macro `global`
        # declaration, relayered to the macrocall module.  flisp additionally
        # exempts the declared name from hygiene renaming, so sibling bare
        # occurrences of the same raw symbol -- references, assignments, and
        # method-def targets -- classify as global in this scope and resolve in
        # the macro's home module.  Declare the relayered global first (it may
        # shadow a same-named identity-mapped parameter, redirecting `orig`'s
        # key), then bind `orig`'s key to a home-module global unless it is
        # already bound or aliased.  A pre-existing non-global binding for the
        # raw name is a genuine hygienic collision and errors, as in the
        # `K"relayered_global"` check during resolution.
        _record_layer!(ctx, ex[1])
        _record_layer!(ctx, ex[2])
        explicit_declare_in_scope!(ctx, scope, ex[2], :global)
        nk = NameKey(ex[1])
        bid = get(scope.vars, nk, nothing)
        if isnothing(bid)
            haskey(scope.arg_aliases, nk) ||
                declare_in_scope!(ctx, scope, ex[1], :global)
        elseif get_binding(ctx, bid).kind !== :global
            throw(LoweringError(ex, string(
                "unhygienic global name `$(nk.name)` conflicts ",
                "with an existing $(_var_str(get_binding(ctx, bid).kind))")))
        end
    elseif k === K"function_decl"
        k1 = kind(ex[1])
        _record_layer!(ctx, ex[1])
        if k1 === K"BindingId"
            b = get_binding(ctx, ex[1])
            @jl_assert b.is_ssa || b.kind === :global (
                ex, "allow local BindingId as function name?")
            get!(scope.binding_assignments, b.id, ex[1]._id)
        elseif k1 === K"Identifier"
            sc = ex[1].context::SyntaxContext
            if !hasattr(ex[1], :mod) && is_flisp_compat(sc) && !is_base_layer(sc) &&
                sc.layer !== ctx.layer &&
                getmeta(ex[1], :expansion_root_method, false)
                # flisp resolves an unescaped method-def name at the root of a
                # hygienic expansion as a plain global of the macro's home module
                # (the layer's module), defining or extending that module's
                # function rather than binding a mangled local.  A nested (e.g.
                # block- or quote-wrapped) def keeps its hygienic renaming.
                nk = NameKey(ex[1])
                haskey(scope.vars, nk) ||
                    (scope.vars[nk] = _new_binding(ctx, ex[1], nk.name, :global;
                                                   mod=sc.layer.mod).id)
            elseif !is_escaped_binding_target(ctx, ex, ex[1])
                hasattr(ex[1], :mod) && explicit_declare_in_scope!(ctx, scope, ex[1], :global)
                get!(scope.assignments, NameKey(ex[1]), ex[1]._id)
                get!(ctx.layer_ids, (ex[1].context::SyntaxContext).layer,
                     length(ctx.layer_ids)+1)
            end
        else
            @jl_assert false (ex, "unknown kind in assignment")
        end
    elseif k in KSet"= constdecl assign_or_constdecl_if_global"
        k1 = kind(ex[1])
        _record_layer!(ctx, ex[1])
        sc = ex[1].context::SyntaxContext
        if is_escaped_binding_target(ctx, ex, ex[1])
            # An `esc`ed target from a nested expansion is not introduced by
            # this expansion; leave it unregistered so it resolves as a
            # reference (see `is_escaped_binding_target`).
        elseif k === K"constdecl" && is_flisp_compat(ex[1]) &&
            is_top_scope(scope) && sc.layer !== ctx.layer
            # flisp gensym-renames an unescaped top-level `const` target in a
            # hygienic expansion, binding a hidden (name-mangled) global in the
            # eval-target module rather than the macro's home.  Mirror that; the
            # binding is invisible outside the expansion, but later unescaped
            # references in the same expansion resolve to it (e.g. CBOOCall
            # reads its `FuncMap` const back in generated methods).
            nk = NameKey(ex[1])
            if !haskey(scope.vars, nk)
                mangled = reserve_module_binding_i(ctx.layer.mod,
                                                   string("#", nk.name, "#"))
                b = _new_binding(ctx, ex[1], mangled, :global;
                                 mod=ctx.layer.mod, is_internal=true)
                scope.vars[nk] = b.id
            end
        elseif k1 === K"BindingId"
            b = get_binding(ctx, ex[1])
            get!(scope.binding_assignments, b.id, ex[1]._id)
        elseif k1 === K"Identifier"
            !hasattr(ex[1], :mod) &&
                get!(scope.assignments, NameKey(ex[1]), ex[1]._id)
        elseif k1 === K"Placeholder"
            # nothing to declare
        else
            @jl_assert false (ex, "unknown kind in assignment")
        end
        if !(k == K"constdecl" && numchildren(ex) == 1)
            _find_scope_decls!(ctx, scope, ex[2])
        end
    elseif needs_resolution(ex) && !(k in KSet"scope_block lambda method_defs")
        for e in children(ex)
            _find_scope_decls!(ctx, scope, e)
        end
    end
    nothing
end

# Produce a complete ScopeInfo and add it to the stack of active scopes.  This
# means finding all variables declared and used in the scope `ex` and generating
# the (identifier,layer)=>binding_id mapping `scope.vars`
function enter_scope!(ctx, ex)
    @jl_assert kind(ex) in KSet"lambda scope_block method_defs" ex
    # Note that generated functions produce lambdas with this false
    is_toplevel_thunk = kind(ex) === K"lambda" && ex.is_toplevel_thunk
    parent_id = (is_toplevel_thunk || isempty(ctx.scope_stack)) ?
        0 : ctx.scopes[ctx.scope_stack[end]].id
    scope = ScopeInfo(ctx, parent_id, ex)

    #---------------------------------------------------------------------------
    # Find explicit decls that may influence assignment assignment resolution
    if kind(ex) === K"lambda"
        for c in children(ex[1])
            @jl_assert kind(c) in KSet"Identifier BindingId Placeholder" c
            explicit_declare_in_scope!(ctx, scope, c, :argument)
        end
        for c in children(ex[2])
            kind(c) === K"Placeholder" && continue
            @jl_assert kind(c) === K"Identifier" c
            sp_id = explicit_declare_in_scope!(ctx, scope, c, :static_parameter)
            p = parent(ctx, scope)
            if !isnothing(p) # usually true, false for generated functions
                ctx.sp_typevars[sp_id] = p.vars[NameKey(c)]
            end
        end
        for c in children(ex)[3:end]
            _find_scope_decls!(ctx, scope, c)
        end
    else
        for c in children(ex)
            _find_scope_decls!(ctx, scope, c)
        end
    end
    push!(ctx.scope_stack, scope.id) # influences resolution below

    #---------------------------------------------------------------------------
    # Find assignment targets, possibly introducing implicit locals and globals
    for (bid, _node_id) in sort!(collect(scope.binding_assignments))
        # Mutable nameless bindings may be introduced in desugaring.  These
        # should be capturable, and may be local to the nearest lambda or
        # global.  Desugaring should ensure these are never used undef.
        b = get_binding(ctx, bid)
        b.lambda_id != 0 || add_lambda_local!(ctx, scope, b)
    end
    for (vk, node_id) in sort!(collect(scope.assignments);
                               by=x->let nk=x[1]; (nk.name, ctx.layer_ids[nk.layer]); end)
        local ex = SyntaxTree(ctx.graph, node_id)
        b = resolve_name(ctx, ex; include_arg_aliases=false)
        if b === nothing
            sc = ex.context::SyntaxContext
            # Top-level assignments are locals in hygienic expansions.  We may
            # need to adjust this, as flisp makes them name-mangled globals.
            hygienic_toplevel = !is_base_layer(sc) && sc.layer !== ctx.layer
            if is_toplevel_thunk && !hygienic_toplevel
                # top-level assignments in no scope and no expansion
                push!(ctx.soft_assignable_globals, vk)
                declare_in_scope!(ctx, top_scope(ctx), ex, :global)
            elseif scope.is_permeable && !hygienic_toplevel &&
                is_defined_and_owned_global(
                    syntax_module(sc), Symbol(vk.name), ctx.world)
                # special soft scope rules: existing global variables are assigned to
                if ctx.enable_soft_scopes
                    push!(ctx.soft_assignable_globals, vk)
                    declare_in_scope!(ctx, top_scope(ctx), ex, :global)
                else
                    declare_in_scope!(ctx, scope, ex, :local; is_ambiguous_local=true)
                end
            else
                declare_in_scope!(ctx, scope, ex, :local)
            end
        elseif b.kind === :global
            if is_toplevel_thunk
                # assign-existing and make visible to soft scope
                push!(ctx.soft_assignable_globals, vk)
            elseif !isnothing(resolve_name(ctx, ex; exclude_toplevel_globals=true,
                                           include_arg_aliases=false)) ||
                (ctx.enable_soft_scopes && scope.is_permeable &&
                vk in ctx.soft_assignable_globals)
                # assign-existing-global if this is an explicit global that
                # isn't at top level, or if the soft scope exception applies
            else
                declare_in_scope!(ctx, scope, ex, :local; is_ambiguous_local = scope.is_permeable)
            end
        elseif b.kind === :static_parameter
            throw(LoweringError(ex, "cannot overwrite a static parameter"))
        elseif b.kind === :local || b.kind === :argument
            # unambiguous assignment to existing variable
        end
    end

    return scope
end

function add_local_decls!(ctx, stmts, srcref, scope)
    # Add local decls to start of block so that closure conversion can
    # initialize if necessary.
    for id in sort!(collect(values(scope.vars)))
        binfo = get_binding(ctx, id)
        if binfo.kind == :local
            push!(stmts, @ast ctx srcref [K"local" binding_ex(ctx, id)])
        end
    end
end

# Resolve a lambda's argument (or static-parameter) list.  These are declaring
# occurrences, so a parameter whose name is shadowed by a body `global`
# declaration must still bind its own arg/sparam slot here even though `vars`
# now maps the name to the shadowing global (see `explicit_declare_in_scope!`).
function resolve_lambda_params(ctx, params, scope)
    isempty(scope.shadowed_params) && return _resolve_scopes(ctx, params, scope)
    mapchildren(ctx, params) do c
        bid = kind(c) === K"Identifier" ?
            get(scope.shadowed_params, NameKey(c), nothing) : nothing
        isnothing(bid) ? _resolve_scopes(ctx, c, scope) :
            newleaf(ctx, c, K"BindingId", bid)
    end
end

function _resolve_scopes(ctx, ex::SyntaxTree,
                         @nospecialize(scope::Union{Nothing, ScopeInfo}))
    k = kind(ex)
    @jl_assert scope isa ScopeInfo || k === K"lambda" ex
    if k == K"Identifier"
        if (mod = get(ex, :mod, nothing); !isnothing(mod))
            return new_global_binding(ctx, ex, ex.name_val, mod)
        end
        b = resolve_name(ctx, ex)
        # flisp-compat: a bare `#self#` that resolves to nothing is the leaked
        # implicit-self idiom; redirect it to the enclosing function's self.
        if isnothing(b) && is_self_hash_leak(ctx, ex, scope)
            return _resolve_scopes(ctx, thisfunction_self_arg(ctx, ex, scope), scope)
        end
        # Unresolved names are assumed global
        if isnothing(b)
            if kind(ex) === K"Identifier" && ex.name_val == "#self#" && is_flisp_compat(ex)
                # A `#self#` that reaches here is a flisp-compat leak site whose
                # enclosing self flisp did not expose (e.g. genuine top level);
                # like flisp, leave it as an undefined global reference.  But do
                # NOT register it in the top scope: `#self#` is never a real user
                # global, and a persistent binding would be found first by a
                # later, legitimately-leakable `#self#` in the same lowering
                # unit, whose leak check only runs when resolution returns nothing.
                return new_global_binding(ctx, ex, ex.name_val, syntax_module(ex))
            end
            gid = declare_in_scope!(ctx, top_scope(ctx), ex, :global)
            b = get_binding(ctx, gid)
        end
        # Body-level @nospecialize sets :nospecialize metadata on identifiers.
        # Propagate this to the binding so the slot gets the nospecialize flag.
        if getmeta(ex, :nospecialize, false) && b.kind === :argument
            b.is_nospecialize = true
        end
        newleaf(ctx, ex, K"BindingId", b.id)
    elseif k === K"BindingId"
        ex
    elseif k == K"softscope"
        newleaf(ctx, ex, K"TOMBSTONE")
    elseif !needs_resolution(ex)
        ex
    elseif k == K"local"
        # Local declarations have a value of `nothing` according to flisp
        # lowering.
        # TODO: Should local decls be disallowed in value position?
        @ast ctx ex (::K"nothing")
    elseif k == K"decl"
        ex_out = mapchildren(e->_resolve_scopes(ctx, e, scope), ctx, ex)
        name = ex_out[1]
        if kind(name) != K"Placeholder"
            binfo = get_binding(ctx, name)
            if binfo.kind == :global && !is_top_scope(enclosing_lambda(ctx, scope))
                throw(LoweringError(ex, "type declarations for global variables must be at top level, not inside a function"))
            end
        end
        id = ex_out[1]
        if kind(id) != K"Placeholder"
            binfo = get_binding(ctx, id)
            if !isnothing(binfo.type) && binfo.kind !== :global
                throw(LoweringError(ex, "multiple type declarations found for `$(binfo.name)`"))
            end
            binfo.type = ex_out[2]._id
        end
        ex_out
    elseif k == K"always_defined"
        resolve_name(ctx, ex[1]).is_always_defined = true
        newleaf(ctx, ex, K"TOMBSTONE")
    elseif k == K"lambda"
        # opaque closures are the exception
        # scope isa ScopeInfo && @jl_assert scope.is_lifted ex
        newscope = enter_scope!(ctx, ex)
        arg_bindings = resolve_lambda_params(ctx, ex[1], newscope)
        sparam_bindings = SyntaxList(ctx)
        for sp in children(ex[2])
            kind(sp) === K"Placeholder" && continue
            # A body `global` may shadow a same-named sparam (see
            # `resolve_lambda_params`); keep the original binding for the
            # parameter list itself.
            bid = kind(sp) === K"Identifier" ?
                get(newscope.shadowed_params, NameKey(sp), nothing) : nothing
            push!(sparam_bindings, isnothing(bid) ?
                  _resolve_scopes(ctx, sp, newscope) :
                  newleaf(ctx, sp, K"BindingId", bid))
        end
        self_id = if numchildren(arg_bindings) === 0
            0
        elseif getmeta(ex[1][1], :is_kwcall_self, false)
            arg_bindings[3].var_id
        else
            arg_bindings[1].var_id
        end
        lambda_bindings = LambdaBindings(self_id, newscope.id, newscope.locals_capt)
        body_stmts = SyntaxList(ctx)
        add_local_decls!(ctx, body_stmts, ex, newscope)
        body = _resolve_scopes(ctx, ex[3], newscope)
        if kind(body) == K"block"
            append!(body_stmts, children(body))
        else
            push!(body_stmts, body)
        end
        ret_var = numchildren(ex) == 4 ?
            _resolve_scopes(ctx, ex[4], newscope) : nothing
        pop!(ctx.scope_stack)

        @ast ctx ex [K"lambda"(;lambda_bindings=lambda_bindings,
                               is_toplevel_thunk=ex.is_toplevel_thunk,
                               toplevel_pure=ex.toplevel_pure)
            arg_bindings
            [K"block" sparam_bindings...]
            [K"block" body_stmts...]
            ret_var
        ]
    elseif k == K"scope_block"
        newscope = enter_scope!(ctx, ex)
        stmts = SyntaxList(ctx)
        add_local_decls!(ctx, stmts, ex, newscope)
        for e in children(ex)
            push!(stmts, _resolve_scopes(ctx, e, newscope))
        end
        pop!(ctx.scope_stack)
        @ast ctx ex [K"block" stmts...]
    elseif k == K"method_defs"
        newscope = enter_scope!(ctx, ex)
        mname = _resolve_scopes(ctx, ex[1], scope)
        tvs = SyntaxList(ctx.graph)
        for tv in children(ex[2]) # hack. flisp: replace-vars
            rhs = _resolve_scopes(ctx, tv[2], newscope)
            if kind(tv[1]) === K"Placeholder"
                @ast ctx tv [K"=" tv[1] rhs]
            else
                bid = declare_in_scope!(ctx, newscope, tv[1], :typevar)
                get_binding(ctx, bid).is_always_defined = true
                deps = Vector{IdTag}()
                _typevar_refs!(deps, ctx, rhs)
                isempty(deps) || (ctx.tv_deps[bid] = deps)
                push!(tvs, @ast ctx tv [K"=" binding_ex(ctx, bid) rhs])
            end
        end
        stmts = SyntaxList(ctx)
        add_local_decls!(ctx, stmts, ex, newscope)
        push!(stmts, _resolve_scopes(ctx, ex[3], newscope))
        pop!(ctx.scope_stack)
        @ast ctx ex [K"method_defs" mname [K"block" tvs...] [K"block" stmts...]]
    elseif k == K"islocal"
        e1 = ex[1]
        islocal = kind(e1) == K"Identifier" &&
            let b = resolve_name(ctx, e1)
                !isnothing(b) && b.kind !== :global
            end
        @ast ctx ex islocal::K"Bool"
    elseif k == K"isglobal"
        e1 = ex[1]
        isglobal = kind(e1) == K"Identifier" &&
            let b = resolve_name(ctx, e1)
                isnothing(b) || b.kind === :global
            end
        @ast ctx ex isglobal::K"Bool"
    elseif k == K"locals"
        stmts = SyntaxList(ctx)
        locals_dict = ssavar(ctx, ex, "locals_dict")
        push!(stmts, @ast ctx ex [K"="
            locals_dict
            [K"call"
                [K"call"
                    "apply_type"::K"core"
                    "Dict"::K"top"
                    "Symbol"::K"core"
                    "Any"::K"core"
                ]
            ]
        ])
        for sid in ctx.scope_stack
            for id in sort!(collect(values(ctx.scopes[sid].vars)))
                binfo = get_binding(ctx, id)
                if binfo.kind == :global || binfo.is_internal
                    continue
                end
                binding = binding_ex(ctx, id)
                push!(stmts, @ast ctx ex [K"if"
                    [K"isdefined" binding]
                    [K"call"
                        "setindex!"::K"top"
                        locals_dict
                        binding
                        binfo.name::K"Symbol"
                    ]
                ])
            end
        end
        push!(stmts, locals_dict)
        newnode(ctx, ex, K"block", stmts)
    elseif k == K"thisfunction"
        return _resolve_scopes(ctx, thisfunction_self_arg(ctx, ex, scope), scope)
    elseif k == K"assert"
        etype = extension_type(ex)
        if etype == "require_existing_locals"
            for v in ex[2:end]
                b = resolve_name(ctx, v)
                if isnothing(b) || !(b.kind in (:local, :argument))
                    throw(LoweringError(v, "`outer` annotations must match with a local variable in an outer scope but no such variable was found"))
                end
            end
        elseif etype == "global_toplevel_only"
            if !is_top_scope(scope)
                e = ex[2][1]
                throw(LoweringError(e, "$(kind(e)) is only allowed in global scope"))
            end
        elseif etype == "toplevel_only"
            if !is_top_scope(enclosing_lambda(ctx, scope))
                e = ex[2][1]
                throw(LoweringError(e, "this syntax is only allowed in top level code"))
            end
        else
            @jl_assert false (ex, "unknown syntax assertion")
        end
        newleaf(ctx, ex, K"TOMBSTONE")
    elseif k === K"relayered_global"
        bid = get(scope.vars, NameKey(ex[1]), nothing)
        !isnothing(bid) && let b = get_binding(ctx, bid)
            b.kind !== :global && throw(LoweringError(ex, string(
                "unhygienic global name `$(NameKey(ex[1]).name)` conflicts ",
                "with an existing $(_var_str(b.kind))")))
        end
        newleaf(ctx, ex, K"TOMBSTONE")
    elseif k == K"function_decl"
        resolved = mapchildren(e->_resolve_scopes(ctx, e, scope), ctx, ex)
        name = resolved[1]
        if kind(name) == K"BindingId"
            bk = get_binding(ctx, name).kind
            if bk == :argument
                throw(LoweringError(name, "Cannot add method to a function argument"))
            elseif bk == :global && !is_top_scope(enclosing_lambda(ctx, scope))
                throw(LoweringError(name, """
                    Global method definition needs to be placed at the top \
                    level, or use `eval()`"""))
            end
        end
        resolved
    elseif k == K"constdecl"
        if !is_top_scope(enclosing_lambda(ctx, scope))
            throw(LoweringError(ex, "unsupported `const` inside function"))
        end
        resolved = mapchildren(e->_resolve_scopes(ctx, e, scope), ctx, ex)
        if kind(resolved[1]) !== K"Placeholder"
            @jl_assert kind(resolved[1]) === K"BindingId" resolved
            if get_binding(ctx, resolved[1].var_id).kind === :local
                throw(LoweringError(ex, "unsupported `const` declaration on local variable"))
            end
        end
        resolved
    elseif k == K"assign_or_constdecl_if_global"
        @jl_assert numchildren(ex) === 2 ex
        id = _resolve_scopes(ctx, ex[1], scope)
        assignment_kind =
            kind(id) === K"Placeholder" ||
            (get_binding(ctx, id).kind !== :global) ? K"=" : K"constdecl"
        @ast ctx ex _resolve_scopes(ctx, [assignment_kind ex[1] ex[2]], scope)
    elseif k === K"global_if_global"
        out = _resolve_scopes(ctx, ex[1], scope)
        get_binding(ctx, out).kind !== :global ? (@ast ctx ex (::K"TOMBSTONE")) :
            @ast ctx ex [K"global" out]
    elseif k == K"cfunction"
        # The bare-symbol `@cfunction` callee (child 2, wrapped by compat.jl in
        # a `K"static_eval"`) is resolved in global scope by construction: flisp
        # looks it up as a global at compile time, invisible to any co-named
        # local. Other callee forms (e.g. a `$`-interpolated runtime closure)
        # are not wrapped in `static_eval` and resolve normally.
        cs = SyntaxList(ctx)
        for (i, e) in enumerate(children(ex))
            if i == 2 && kind(e) === K"static_eval" && numchildren(e) === 1 &&
                    kind(e[1]) === K"Identifier"
                push!(cs, @ast ctx e [K"static_eval"(e) resolve_as_global(ctx, e[1])])
            else
                push!(cs, _resolve_scopes(ctx, e, scope))
            end
        end
        @ast ctx ex [K"cfunction" cs...]
    else
        mapchildren(e->_resolve_scopes(ctx, e, scope), ctx, ex)
    end
end

function _resolve_scopes(ctx, exs::AbstractVector, scope)
    out = SyntaxList(ctx)
    for e in exs
        push!(out, _resolve_scopes(ctx, e, scope))
    end
    out
end

#-------------------------------------------------------------------------------
# Sub-pass to compute additional information about variable usage as required
# by closure conversion, etc
struct ClosureBindings
    name_stack::Vector{String}      # Names of functions the closure is nested within
    lambdas::Vector{LambdaBindings} # Bindings for each method of the closure
    capt_sp::Set{IdTag}
end

# `binding` is that in `function_decl`, `method_defs[1]`, `method[1]`,
# `function_type[1]` when local
struct ClosureKey
    binding::IdTag
    lam::ScopeId
end

ClosureBindings(name_stack) =
    ClosureBindings(name_stack, Vector{LambdaBindings}(), Set{IdTag}())

struct VariableAnalysisContext{Attrs} <: AbstractLoweringContext
    graph::SyntaxGraph{Attrs}
    layer::ScopeLayer
    bindings::Bindings
    scopes::Vector{ScopeInfo}
    lambda_bindings::LambdaBindings
    lifted::Bool
    # Stack of method definitions for closure naming
    method_def_stack::SyntaxList{Attrs, Vector{NodeId}}
    closure_key_stack::Vector{ClosureKey}
    # Collection of information about each closure, principally which methods
    # are part of the closure (and hence captures).
    closure_bindings::Dict{ClosureKey,ClosureBindings}
    sp_typevars::Dict{IdTag, IdTag}
    tv_deps::Dict{IdTag, Vector{IdTag}}
    # Prevents infinite loops when analyzing a binding's type
    types_in_analysis::Set{IdTag}
end

function init_closure_bindings!(ctx, fname)
    bid = fname.var_id::IdTag
    ck = closure_key(ctx, fname)
    @jl_assert get_binding(ctx, bid).kind === :local fname
    get!(ctx.closure_bindings, ck) do
        name_stack = Vector{String}()
        for parentname in ctx.method_def_stack
            if kind(parentname) == K"BindingId"
                push!(name_stack, get_binding(ctx, parentname).name)
            end
        end
        push!(name_stack, get_binding(ctx, bid).name)
        ClosureBindings(name_stack)
    end
end

# Search `ex` for a binding that is illegal in a compile-time-evaluated position
# (`K"static_eval"` / `K"foreignsymbol"`).  Globals and static parameters are
# always fine.  When `reject_lambda_id` is given (static_eval positions), only
# genuine locals of that lambda are rejected: a binding captured from an
# enclosing scope is deferred to codegen's static evaluation, which understands
# closure capture (matching flisp, which leaves ccall/cfunction return- and
# argument-type expressions unchecked at lowering time).  When it is `nothing`
# (foreignsymbol, i.e. the ccall/cglobal function name and library expression),
# any local is rejected -- except a top-level local referenced from a global
# method, which lowering's expr-builder path supports (upstream 4f56102cb9).
function find_any_local_binding(ctx, ex; reject_lambda_id=nothing)
    k = kind(ex)
    if k == K"BindingId"
        b = get_binding(ctx, ex.var_id)
        bkind = b.kind
        if bkind != :global && bkind != :static_parameter
            if !isnothing(reject_lambda_id)
                b.lambda_id === reject_lambda_id && return ex
            else
                lam = ctx.scopes[ctx.lambda_bindings.scope_id]
                if is_top_scope(lam) ||
                    !(b.lambda_id == top_scope(ctx).id &&
                    enclosing_lambda(ctx, parent(ctx, lam)).id == top_scope(ctx).id)
                    return ex
                end
            end
        end
    elseif !is_leaf(ex) && !is_quoted(ex)
        for e in children(ex)
            r = find_any_local_binding(ctx, e; reject_lambda_id)
            if !isnothing(r)
                return r
            end
        end
    end
    return nothing
end

# Mark bindings captured from an enclosing scope which appear inside a
# `K"static_eval"` type expression, so closure conversion rewrites them into
# `captured_local` interpolations.  Same-function locals are already rejected
# before this runs; globals, static parameters and SSA values need no capture.
function capture_static_eval_bindings!(ctx, ex)
    k = kind(ex)
    if k == K"BindingId"
        b = get_binding(ctx, ex.var_id)
        if b.kind !== :global && b.kind !== :static_parameter && !b.is_ssa
            ensure_captured!(ctx, ctx.scopes[ctx.lambda_bindings.scope_id], b)
        end
    elseif !is_leaf(ex) && !is_quoted(ex)
        for e in children(ex)
            capture_static_eval_bindings!(ctx, e)
        end
    end
    nothing
end

function add_assign!(b::BindingInfo)
    b.is_assigned_once = !b.is_assigned
    b.is_assigned = true
end

# When a closure captures `T` and `T`'s typevar bound references `S`, it must
# capture `S` too
function expand_captured_sp_deps!(ctx, cb::ClosureBindings, scope)
    sps = copy(cb.capt_sp)
    for lb in cb.lambdas, (id, is_capt) in lb.locals_capt
        is_capt && get_binding(ctx, id).kind === :static_parameter && push!(sps, id)
    end
    todo = collect(sps)
    while !isempty(todo)
        sp = pop!(todo)
        owner = ctx.scopes[get_binding(ctx, sp).lambda_id]
        for dep_tv in get(ctx.tv_deps, ctx.sp_typevars[sp], ())
            # The sparam for dep_tv in the same lambda that owns `sp`
            dep_sp = nothing
            for id in keys(owner.locals_capt)
                b = get_binding(ctx, id)
                if b.kind === :static_parameter &&
                        get(ctx.sp_typevars, b.id, IdTag(0)) == dep_tv
                    dep_sp = id
                    break
                end
            end
            isnothing(dep_sp) && throw(LoweringError(
                binding_ex(ctx, dep_tv), "unimplemented capture in sparam bounds"))
            dep_sp in sps && continue
            push!(sps, dep_sp)
            push!(cb.capt_sp, dep_sp)
            ensure_captured!(ctx, scope, get_binding(ctx, dep_sp))
            push!(todo, dep_sp)
        end
    end
end

function closure_key(ctx, ex)
    @jl_assert kind(ex) === K"BindingId" ex
    ClosureKey(ex.var_id::IdTag, ctx.lambda_bindings.scope_id)
end
function current_closure_bindings(ctx)
    isempty(ctx.closure_key_stack) && return nothing
    get(ctx.closure_bindings, ctx.closure_key_stack[end], nothing)
end

# Update ctx.bindings metadata based on binding usage
function analyze_variables!(ctx, ex)
    k = kind(ex)
    if k == K"BindingId"
        b = get_binding(ctx, ex)
        b.is_read = true
        # The type of typed locals is invisible in the previous pass,
        # but is filled in here.
        scope = ctx.scopes[ctx.lambda_bindings.scope_id]
        ensure_captured!(ctx, scope, b)
        # b.kind === :static_parameter && ensure_captured!(ctx, scope, b)
        @jl_assert (b.kind === :global || b.kind === :typevar || b.is_ssa ||
            haskey(ctx.lambda_bindings.locals_capt, b.id)) ex binding_ex(ctx, b.id)
        if b.kind === :static_parameter && ctx.lifted
            cb = current_closure_bindings(ctx)
            isnothing(cb) || push!(cb.capt_sp, b.id)
        end
        if (b.kind === :local || b.kind === :argument) && !isnothing(b.type) &&
            !(b.id in ctx.types_in_analysis)
            push!(ctx.types_in_analysis, b.id)
            analyze_variables!(ctx, binding_type_ex(ctx, b))
            delete!(ctx.types_in_analysis, b.id)
        end
    elseif k == K"Identifier"
        @jl_assert false ex
    elseif k == K"break" && numchildren(ex) >= 2
        # For break with value, only analyze the value expression (second child), not the label
        # This must come BEFORE !needs_resolution check since K"break" is in is_quoted
        analyze_variables!(ctx, ex[2])
        return
    elseif !needs_resolution(ex)
        return
    elseif k == K"static_eval" || k == K"foreignsymbol"
        reject_lambda_id = k == K"static_eval" ?
            ctx.lambda_bindings.scope_id : nothing
        badvar = find_any_local_binding(ctx, ex[1]; reject_lambda_id)
        if !isnothing(badvar)
            default = k == K"foreignsymbol" ?
                "function name and library expression" : "syntax"
            name_hint = getmeta(ex, :name_hint, default)::String
            throw(LoweringError(badvar, "$(name_hint) cannot reference local variable"))
        end
        analyze_variables!(ctx, ex[1])
        if k == K"static_eval"
            # Bindings captured from an enclosing scope are legal in a
            # static_eval type expression: mark them captured so closure
            # conversion rewrites them into `captured_local` interpolations,
            # which are spliced into the method at definition time (matching
            # flisp, which builds such method bodies as spliced templates).
            capture_static_eval_bindings!(ctx, ex[1])
        end
        return
    elseif k == K"local" || k == K"global"
        # Presence of BindingId within local/global is ignored.
        return
    elseif k == K"="
        lhs = ex[1]
        if kind(lhs) != K"Placeholder"
            b = get_binding(ctx, lhs)
            add_assign!(b)
            scope = ctx.scopes[ctx.lambda_bindings.scope_id]
            ensure_captured!(ctx, scope, b)
            if !isnothing(b.type)
                # Assignments introduce a variable's type later during closure
                # conversion, but we must model that explicitly here.
                analyze_variables!(ctx, binding_type_ex(ctx, b))
            end
        end
        analyze_variables!(ctx, ex[2])
    elseif k == K"function_decl"
        name = ex[1]
        b = get_binding(ctx, name)
        if b.kind === :local
            init_closure_bindings!(ctx, name)
        end
        add_assign!(b)
    elseif k == K"function_type"
        if kind(ex[1]) != K"BindingId" || get_binding(ctx, ex[1]).kind !== :local
            analyze_variables!(ctx, ex[1])
        end
    elseif k == K"constdecl"
        if kind(ex[1]) !== K"Placeholder"
            b = get_binding(ctx, ex[1])
            b.is_const = true
            add_assign!(b)
        end
        analyze_variables!(ctx, ex[2])
    elseif k == K"call"
        name = ex[1]
        if kind(name) == K"BindingId"
            get_binding(ctx, name).is_called = true
        end
        foreach(e->analyze_variables!(ctx, e), children(ex))
    elseif k == K"method_defs"
        push!(ctx.method_def_stack, ex[1])
        is_closure = kind(ex[1]) == K"BindingId" &&
            get_binding(ctx, ex[1]).kind === :local
        ctx2 = VariableAnalysisContext(
            ctx.graph, ctx.layer, ctx.bindings, ctx.scopes,
            ctx.lambda_bindings, true, ctx.method_def_stack,
            ctx.closure_key_stack,
            ctx.closure_bindings, ctx.sp_typevars, ctx.tv_deps,
            ctx.types_in_analysis)
        if is_closure
            push!(ctx.closure_key_stack, closure_key(ctx2, ex[1]))
            cb = init_closure_bindings!(ctx2, ex[1])
            scope = ctx.scopes[ctx2.lambda_bindings.scope_id]
        end
        analyze_variables!(ctx2, ex[2])
        analyze_variables!(ctx2, ex[3])
        if is_closure
            # All captures are known now; close them over typevar-bound deps
            expand_captured_sp_deps!(ctx, cb, scope)
            pop!(ctx.closure_key_stack)
        end
        pop!(ctx.method_def_stack)
    elseif k == K"_opaque_closure"
        name = ex[1]
        init_closure_bindings!(ctx, name)
        push!(ctx.method_def_stack, name)
        push!(ctx.closure_key_stack, closure_key(ctx, ex[1]))
        analyze_variables!(ctx, ex[2])
        analyze_variables!(ctx, ex[3])
        analyze_variables!(ctx, ex[4])
        analyze_variables!(ctx, ex[9])
        pop!(ctx.method_def_stack)
        pop!(ctx.closure_key_stack)
    elseif k == K"lambda"
        lambda_bindings = ex.lambda_bindings::LambdaBindings
        if !ex.is_toplevel_thunk && !isempty(ctx.closure_key_stack)
            # Record all lambdas for the same closure type in one place
            ck = last(ctx.closure_key_stack)
            if get_binding(ctx, ck.binding).kind === :local
                push!(ctx.closure_bindings[ck].lambdas, lambda_bindings)
            end
        end
        let ctx2 = VariableAnalysisContext(
            ctx.graph, ctx.layer, ctx.bindings, ctx.scopes,
            lambda_bindings, false, ctx.method_def_stack,
            ctx.closure_key_stack, ctx.closure_bindings,
            ctx.sp_typevars, ctx.tv_deps, ctx.types_in_analysis)
            foreach(e->analyze_variables!(ctx2, e), ex[3:end])
        end
    else
        foreach(e->analyze_variables!(ctx, e), children(ex))
    end
    nothing
end

function resolve_scopes(ctx::ScopeResolutionContext, ex)
    if kind(ex) != K"lambda"
        # Wrap in a top level thunk if we're not already expanding a lambda.
        # (Maybe this should be done elsewhere?)
        ex = @ast ctx ex [K"lambda"(is_toplevel_thunk=true, toplevel_pure=false)
            [K"block"]
            [K"block"]
            ex
        ]
    end
    _resolve_scopes(ctx, ex, nothing)
end

ensure_scope_attributes!(graph) = ensure_attributes!(
    ensure_desugaring_attributes!(graph),
    lambda_bindings=LambdaBindings)

"""
This pass analyzes scopes and the names (locals/globals etc) used within them.

Names of kind `K"Identifier"` are transformed into binding identifiers of
kind `K"BindingId"`. The associated `Bindings` table in the context records
metadata about each binding.

This pass also records the set of binding IDs used locally within the
enclosing lambda form and information about variables captured by closures.
"""
@fzone "JL: resolve_scopes" function resolve_scopes(ctx::DesugaringContext, ex;
                                                    soft_scope::Union{Nothing,Bool}=nothing,
                                                    world::UInt=ctx.world)
    graph = ensure_scope_attributes!(copy_attrs(ctx.graph))
    ex = reparent(graph, ex)
    enable_soft_scopes = soft_scope !== nothing ? soft_scope : contains_softscope_marker(ex)
    ctx2 = ScopeResolutionContext(graph, ctx.layer, ctx.bindings,
                                  Dict{ScopeLayer, Int}(),
                                  Vector{ScopeInfo}(), Vector{ScopeId}(),
                                  Set{NameKey}(), Dict{IdTag, IdTag}(),
                                  Dict{IdTag, Vector{IdTag}}(),
                                  enable_soft_scopes,
                                  world)
    ex2 = resolve_scopes(ctx2, ex)
    ctx3 = VariableAnalysisContext(graph, ctx2.layer, ctx2.bindings,
                                   ctx2.scopes, ex2.lambda_bindings, true,
                                   SyntaxList(graph), Vector{ClosureKey}(),
                                   Dict{ClosureKey,ClosureBindings}(),
                                   ctx2.sp_typevars, ctx2.tv_deps, Set{IdTag}())
    analyze_variables!(ctx3, ex2)
    analyze_def_and_use!(ctx3, ex2)
    ctx3, ex2
end
