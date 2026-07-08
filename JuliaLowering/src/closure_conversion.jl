struct ClosureInfo{Attrs}
    # Global name of the type of the closure
    type_name::SyntaxTree{Attrs}
    # Names of fields for use with getfield, in order
    field_names::SyntaxList{Attrs, Vector{NodeId}}
    # Map from the original BindingId of closed-over vars to the index of the
    # associated field in the closure type.
    field_inds::Dict{IdTag,Int}
end

struct ClosureConversionCtx{Attrs} <: AbstractLoweringContext
    graph::SyntaxGraph{Attrs}
    bindings::Bindings
    mod::Module
    closure_bindings::Dict{IdTag,ClosureBindings}
    capture_rewriting::Union{Nothing,ClosureInfo{Attrs},
                             SyntaxList{Attrs, Vector{NodeId}}}
    lambda_bindings::LambdaBindings
    # True if we're in a section of code which preserves top-level sequencing
    # such that closure types can be emitted inline with other code.
    is_toplevel_seq_point::Bool
    # True if this expression should not have toplevel effects, namely, it
    # should not declare the globals it references.  This allows generated
    # functions to refer to globals that have already been declared, without
    # triggering the "function body AST not pure" error.
    toplevel_pure::Bool
    toplevel_stmts::SyntaxList{Attrs, Vector{NodeId}}
    closure_infos::Dict{IdTag,ClosureInfo{Attrs}}
end

function current_lambda_bindings(ctx::ClosureConversionCtx)
    ctx.lambda_bindings
end

# Access captured variable from inside a closure
function captured_var_access(ctx, ex)
    cap_rewrite = ctx.capture_rewriting
    if cap_rewrite isa ClosureInfo
        field_sym = cap_rewrite.field_names[cap_rewrite.field_inds[ex.var_id]]
        @ast ctx ex [K"call"
            "getfield"::K"core"
            binding_ex(ctx, current_lambda_bindings(ctx).self)
            field_sym
        ]
    else
        interpolations = cap_rewrite
        @jl_assert !isnothing(cap_rewrite) ex
        if isempty(interpolations) || !is_same_identifier_like(interpolations[end], ex)
            push!(interpolations, ex)
        end
        @ast ctx ex [K"captured_local" length(interpolations)::K"Integer"]
    end
end

function get_box_contents(ctx::ClosureConversionCtx, var, box_ex)
    undef_var = new_local_binding(ctx, var, get_binding(ctx, var.var_id).name;
                                  is_used_undef=true)
    @ast ctx var [K"block"
        box := box_ex
        # Lower in an UndefVar check to a similarly named variable
        # (ref #20016) so that closure lowering Box introduction
        # doesn't impact the error message and the compiler is expected
        # to fold away the extraneous null check
        #
        # TODO: Ideally the runtime would rely on provenance info for
        # this error and we can remove the isdefined check.
        [K"if" [K"call"
                "isdefined"::K"core"
                box
                "contents"::K"Symbol"
            ]
            ::K"TOMBSTONE"
            [K"block"
                 [K"newvar" undef_var]
                 undef_var
            ]
        ]
        [K"call"
            "getfield"::K"core"
            box
            "contents"::K"Symbol"
        ]
    ]
end

# Convert `ex` to `type` by calling `convert(type, ex)` when necessary.
#
# Used for converting the right hand side of an assignment to a typed local or
# global and for converting the return value of a function call to the declared
# return type.
function convert_for_type_decl(ctx, srcref, ex, type, do_typeassert)
    # Use a slot to permit union-splitting this in inference
    tmp = new_local_binding(ctx, srcref, "tmp", is_always_defined=true)

    @ast ctx srcref [K"block"
        type_tmp := type
        # [K"=" type_ssa renumber_assigned_ssavalues(type)]
        [K"=" tmp ex]
        [K"if"
            [K"call" "isa"::K"core" tmp type_tmp]
            (::K"nothing")
            [K"="
                tmp
                if do_typeassert
                    [K"call"
                        "typeassert"::K"core"
                        [K"call" "convert"::K"top" type_tmp tmp]
                        type_tmp
                    ]
                else
                    [K"call" "convert"::K"top" type_tmp tmp]
                end
            ]
        ]
        tmp
    ]
end

# TODO: Avoid producing redundant calls to declare_global
function make_globaldecl(ctx, src_ex, mod, name, strong=false, type=nothing)
    decl = @ast ctx src_ex [K"block"
        [K"call"
            "declare_global"::K"core"
            mod::K"Value" name::K"Symbol" strong::K"Bool"
            type
        ]
        (::K"latestworld")
        (::K"nothing")
    ]
    ctx.toplevel_pure && return newleaf(ctx, decl, K"TOMBSTONE")
    if !ctx.is_toplevel_seq_point
        push!(ctx.toplevel_stmts, decl)
        newleaf(ctx, decl, K"TOMBSTONE")
    else
        return decl
    end
end

function convert_global_assignment(ctx, ex, var, rhs0)
    binfo = get_binding(ctx, var)
    @jl_assert binfo.kind == :global ex var
    stmts = SyntaxList(ctx)
    decl = make_globaldecl(ctx, ex, binfo.mod, binfo.name, true)
    if kind(decl) !== K"TOMBSTONE"
        push!(stmts, decl)
    end
    rhs1 = if is_simple_atom(ctx, rhs0)
        rhs0
    else
        tmp = ssavar(ctx, rhs0)
        push!(stmts, @ast ctx rhs0 [K"=" tmp rhs0])
        tmp
    end
    rhs = if binfo.is_const && isnothing(binfo.type)
        # const global assignments without a type declaration don't need us to
        # deal with the binding type at all.
        rhs1
    else
        type_var = ssavar(ctx, ex, "binding_type")
        push!(stmts, @ast ctx ex [K"="
            type_var
            [K"call"
                "get_binding_type"::K"core"
                binfo.mod::K"Value"
                binfo.name::K"Symbol"
            ]
        ])
        do_typeassert = false # Global assignment type checking is done by the runtime
        convert_for_type_decl(ctx, ex, rhs1, type_var, do_typeassert)
    end
    push!(stmts, @ast ctx ex [K"=" var rhs])
    @ast ctx ex [K"block"
        stmts...
        rhs1
    ]
end

# Convert assignment to a closed variable to a `setfield!` call and generate
# `convert` calls for variables with declared types.
#
# When doing this, the original value needs to be preserved, to ensure the
# expression `a=b` always returns exactly `b`.
function convert_assignment(ctx, ex)
    var = ex[1]
    rhs0 = _convert_closures(ctx, ex[2])
    if kind(var) == K"Placeholder"
        return @ast ctx ex [K"=" var rhs0]
    end
    @jl_assert kind(var) == K"BindingId" ex
    binfo = get_binding(ctx, var)
    if binfo.kind == :global
        convert_global_assignment(ctx, ex, var, rhs0)
    else
        @jl_assert binfo.kind == :local || binfo.kind == :argument ex
        boxed = is_boxed(binfo)
        if isnothing(binfo.type) && !boxed
            @ast ctx ex [K"=" var rhs0]
        else
            # Typed local
            tmp_rhs0 = ssavar(ctx, rhs0)
            rhs = isnothing(binfo.type) ? tmp_rhs0 :
                convert_for_type_decl(
                    ctx, ex, tmp_rhs0,
                    _convert_closures(ctx, binding_type_ex(ctx, binfo)),
                    true)
            assignment = if boxed
                @ast ctx ex [K"call"
                    "setfield!"::K"core"
                    is_self_captured(ctx, var) ? captured_var_access(ctx, var) : var
                    "contents"::K"Symbol"
                    rhs
                ]
            else
                @ast ctx ex [K"=" var rhs]
            end
            @ast ctx ex [K"block"
                [K"=" tmp_rhs0 rhs0]
                assignment
                tmp_rhs0
            ]
        end
    end
end

# Compute fields for a closure type, one field for each captured variable.
function closure_type_fields(ctx, srcref, closure_binds, is_opaque)
    capture_ids = Set{IdTag}()
    for lambda_bindings in closure_binds.lambdas
        for (id, is_capt) in lambda_bindings.locals_capt
            is_capt && push!(capture_ids, id)
        end
    end
    # sort here to avoid depending on undefined Set iteration order
    capture_ids = sort!(collect(capture_ids))

    field_syms = SyntaxList(ctx)
    if is_opaque
        field_orig_bindings = capture_ids
        # For opaque closures we don't try to generate sensible names for the
        # fields as there's no closure type to generate.
        for i in eachindex(field_orig_bindings)
            push!(field_syms, @ast ctx srcref i::K"Integer")
        end
    else
        field_names = Dict{String,IdTag}()
        for id in capture_ids
            binfo = get_binding(ctx, id)
            # We name each field of the closure after the variable which was closed
            # over, for clarity. Adding a suffix can be necessary when collisions
            # occur due to macro expansion and generated bindings
            name0 = binfo.name
            name = name0
            i = 1
            while haskey(field_names, name)
                name = "$name0#$i"
                i += 1
            end
            field_names[name] = id
        end
        field_orig_bindings = Vector{IdTag}()
        for (name,id) in sort!(collect(field_names))
            push!(field_syms, @ast ctx srcref name::K"Symbol")
            push!(field_orig_bindings, id)
        end
    end
    field_inds = Dict{IdTag,Int}()
    field_is_box = Vector{Bool}()
    for (i,id) in enumerate(field_orig_bindings)
        push!(field_is_box, is_boxed(ctx, id))
        field_inds[id] = i
    end

    return field_syms, field_orig_bindings, field_inds, field_is_box
end

# Return a thunk which creates a new type for a closure with `field_syms` named
# fields. The new type will be named `name_str` which must be an unassigned
# name in the module. `sparam_names` are the names of any static parameters of
# enclosing methods captured by the closure's method signatures; these become
# leading type parameters of the closure type (see
# `convert_closure_sig_sparams`).
function type_for_closure(ctx::ClosureConversionCtx, srcref, name_str, field_syms,
                          field_is_box, sparam_names)
    # New closure types always belong to the module we're expanding into - they
    # need to be serialized there during precompile.
    mod = ctx.mod
    type_binding = new_global_binding(ctx, srcref, name_str, mod)
    type_ex = @ast ctx srcref [K"call"
        #"_call_latest"::K"core"
        eval_closure_type::K"Value"
        ctx.mod::K"Value"
        name_str::K"Symbol"
        [K"call" "svec"::K"core" field_syms...]
        [K"call" "svec"::K"core" [f::K"Bool" for f in field_is_box]...]
        if !isempty(sparam_names)
            [K"call" "svec"::K"core" [n::K"Symbol" for n in sparam_names]...]
        end
    ]
    type_ex, type_binding
end

# No box needed for:
# - non-captured vars
# - static params (can't be reassigned)
# - any local our optimizations have determined to be unboxed
function is_boxed(binfo::BindingInfo)
    binfo.kind === :static_parameter && return false
    binfo.unboxed && return false
    binfo.kind === :argument && !binfo.is_assigned && return false
    return binfo.is_captured
end

function is_boxed(ctx, x)
    is_boxed(get_binding(ctx, x))
end

# Is captured in the closure's `self` argument
function is_self_captured(ctx, x)
    get(ctx.lambda_bindings.locals_capt, _binding_id(x), false)
end

function _rewrite_sig_sparams(ctx, ex, closure_id, sparam_tv_inds, tvs)
    k = kind(ex)
    if k == K"BindingId"
        i = get(sparam_tv_inds, ex.var_id, nothing)
        isnothing(i) ? ex : tvs[i]
    elseif k == K"function_type" && kind(ex[1]) == K"BindingId" &&
            ex[1].var_id == closure_id
        # The closure type in argument position is constrained by the new
        # TypeVars, allowing dispatch to re-bind them from the type parameters
        # applied at closure creation time.
        @ast ctx ex [K"call" "apply_type"::K"core" ex tvs...]
    elseif k == K"lambda" || is_leaf(ex) || is_quoted(ex)
        # References within the closure's method bodies are handled by ordinary
        # capture conversion, not here.
        ex
    elseif k == K"call" && kind(ex[1]) == K"core" && ex[1].name_val == "svec" &&
            numchildren(ex) == 4 && kind(ex[3]) == K"call" &&
            kind(ex[4]) == K"SourceLocation"
        # Method signature metadata `svec(svec(arg_types...), svec(sparams...),
        # location)` (see `method_def_expr`): append the new TypeVars as
        # trailing static parameters of the method.
        @ast ctx ex [K"call"
            ex[1]
            _rewrite_sig_sparams(ctx, ex[2], closure_id, sparam_tv_inds, tvs)
            [K"call"(ex[3]) ex[3][1:end]... tvs...]
            ex[4]
        ]
    else
        mapchildren(e->_rewrite_sig_sparams(ctx, e, closure_id, sparam_tv_inds, tvs),
                    ctx, ex)
    end
end

# flisp: the `capt-sp` parts of `cl-convert`'s local `method` case
#
# A closure's method signatures are emitted at top level where the static
# parameters of enclosing methods can't be accessed, so each such static
# parameter referenced by the signatures (recorded in
# `ClosureBindings.sig_sparams`) is turned into a fresh `TypeVar` which becomes
#  * a trailing static parameter of each of the closure's methods, substituted
#    for signature references to the original static parameter, and
#  * a leading type parameter of the closure type, applied at closure creation
#    time (see the `K"function_decl"` case of `_convert_closures`).
#
# For example, with `T` a static parameter of an enclosing method, the methods
# of `g = e::T -> e` become methods `(::#Clo{T′})(e::T′) where T′` of the
# closure type `#Clo`, and the closure itself is created as `new(#Clo{T})` so
# that dispatch re-binds `T′` per closure instance.
function convert_closure_sig_sparams(ctx, ex, closure_id, sig_sparams)
    tvs = SyntaxList(ctx)
    stmts = SyntaxList(ctx)
    sparam_tv_inds = Dict{IdTag,Int}()
    for (i, id) in enumerate(sig_sparams)
        name = get_binding(ctx, id).name
        tv = ssavar(ctx, ex, name)
        push!(stmts, @ast ctx ex [K"=" tv
            [K"call" "TypeVar"::K"core" name::K"Symbol"]])
        push!(tvs, tv)
        sparam_tv_inds[id] = i
    end
    @ast ctx ex [K"block"
        stmts...
        _rewrite_sig_sparams(ctx, ex, closure_id, sparam_tv_inds, tvs)
    ]
end

# Map the children of `ex` through _convert_closures, lifting any toplevel
# closure definition statements to occur before the other content of `ex`.
function map_cl_convert(ctx::ClosureConversionCtx, ex, toplevel_preserving)
    if ctx.is_toplevel_seq_point && !toplevel_preserving
        toplevel_stmts = SyntaxList(ctx)
        ctx2 = ClosureConversionCtx(ctx.graph, ctx.bindings, ctx.mod,
                                    ctx.closure_bindings, ctx.capture_rewriting, ctx.lambda_bindings,
                                    false, ctx.toplevel_pure, toplevel_stmts, ctx.closure_infos)
        res = mapchildren(e->_convert_closures(ctx2, e), ctx2, ex)
        if isempty(toplevel_stmts)
            res
        else
            @ast ctx ex [K"block"
                toplevel_stmts...
                res
            ]
        end
    else
        mapchildren(e->_convert_closures(ctx, e), ctx, ex)
    end
end

function _convert_closures(ctx::ClosureConversionCtx, ex)
    k = kind(ex)
    if k == K"BindingId"
        access = is_self_captured(ctx, ex) ? captured_var_access(ctx, ex) : ex
        if is_boxed(ctx, ex)
            get_box_contents(ctx, ex, access)
        else
            access
        end
    elseif is_leaf(ex) || k == K"inert" || k == K"syntaxinert" || k == K"static_eval"
        ex
    elseif k == K"="
        convert_assignment(ctx, ex)
    elseif k == K"isdefined"
        # Convert isdefined expr to function for closure converted variables
        var = ex[1]
        binfo = get_binding(ctx, var)
        if is_boxed(binfo)
            access = is_self_captured(ctx, var) ? captured_var_access(ctx, var) : var
            @ast ctx ex [K"call"
                "isdefined"::K"core"
                access
                "contents"::K"Symbol"
            ]
        elseif binfo.is_always_defined || is_self_captured(ctx, var)
            # Captured but unboxed vars are always defined
            @ast ctx ex true::K"Bool"
        elseif binfo.kind == :global
            # Normal isdefined won't work for globals (#56985)
            @ast ctx ex [K"call"
                "isdefinedglobal"::K"core"
                ctx.mod::K"Value"
                binfo.name::K"Symbol"
                false::K"Bool"]
        else
            ex
        end
    elseif k == K"decl"
        @jl_assert kind(ex[1]) == K"BindingId" ex
        binfo = get_binding(ctx, ex[1])
        if binfo.kind == :global
            # flisp has this, but our K"assert" handling is in a previous pass
            # [K"assert" "toplevel_only"::K"Symbol" [K"syntaxinert" ex]]
            make_globaldecl(ctx, ex, binfo.mod, binfo.name, true, _convert_closures(ctx, ex[2]))
        else
            newleaf(ctx, ex, K"TOMBSTONE")
        end
    elseif k == K"global"
        # Leftover `global` forms become weak globals.
        mod, name = if kind(ex[1]) == K"BindingId"
            binfo = get_binding(ctx, ex[1])
            @jl_assert binfo.kind == :global ex
            binfo.mod, binfo.name
        else
            # See note about using eval on Expr(:global/:const, GlobalRef(...))
            @jl_assert ex[1].value isa GlobalRef ex[1]
            ex[1].value.mod, String(ex[1].value.name)
        end
        @ast ctx ex [K"unused_only" make_globaldecl(ctx, ex, mod, name, false)]
    elseif k == K"local"
        var = ex[1]
        binfo = get_binding(ctx, var)
        if is_boxed(binfo)
            @ast ctx ex [K"=" var [K"call" "Box"::K"core"]]
        elseif !binfo.is_always_defined
            @ast ctx ex [K"newvar" var]
        else
            newleaf(ctx, ex, K"TOMBSTONE")
        end
    elseif k == K"lambda"
        closure_convert_lambda(ctx, ex)
    elseif k == K"function_decl"
        func_name = ex[1]
        @jl_assert kind(func_name) == K"BindingId" ex
        func_name_id = func_name.var_id
        if haskey(ctx.closure_bindings, func_name_id)
            closure_info = get(ctx.closure_infos, func_name_id, nothing)
            needs_def = isnothing(closure_info)
            if needs_def
                closure_binds = ctx.closure_bindings[func_name_id]
                field_syms, field_orig_bindings, field_inds, field_is_box =
                    closure_type_fields(ctx, ex, closure_binds, false)
                name_str = reserve_module_binding_i(
                    ctx.mod,
                    string("#", join(closure_binds.name_stack, "#"), "##"))
                sparam_names = [get_binding(ctx, id).name
                                for id in closure_binds.sig_sparams]
                closure_type_def, closure_type_ =
                    type_for_closure(ctx, ex, name_str, field_syms, field_is_box,
                                     sparam_names)
                if !ctx.is_toplevel_seq_point
                    push!(ctx.toplevel_stmts, closure_type_def)
                    push!(ctx.toplevel_stmts, @ast ctx ex (::K"latestworld_if_toplevel"))
                    closure_type_def = nothing
                end
                closure_info = ClosureInfo(closure_type_, field_syms, field_inds)
                ctx.closure_infos[func_name_id] = closure_info
                type_params = SyntaxList(ctx)
                # Captured static parameters used in the closure's method
                # signatures become leading type parameters of the closure type
                for id in closure_binds.sig_sparams
                    sp_val = binding_ex(ctx, id)
                    if is_self_captured(ctx, sp_val)
                        sp_val = captured_var_access(ctx, sp_val)
                    end
                    push!(type_params, sp_val)
                end
                init_closure_args = SyntaxList(ctx)
                for (id, boxed) in zip(field_orig_bindings, field_is_box)
                    field_val = binding_ex(ctx, id)
                    if is_self_captured(ctx, field_val)
                        # Access from outer closure if necessary but do not
                        # unbox to feed into the inner nested closure.
                        field_val = captured_var_access(ctx, field_val)
                    end
                    push!(init_closure_args, field_val)
                    if !boxed
                        push!(type_params, @ast ctx ex [K"call"
                              "_typeof_captured_variable"::K"core"
                              field_val])
                    end
                end
                @ast ctx ex [K"block"
                    closure_type_def
                    (::K"latestworld_if_toplevel")
                    closure_type := if isempty(type_params)
                        closure_type_
                    else
                        [K"call" "apply_type"::K"core" closure_type_ type_params...]
                    end
                    closure_val := [K"new"
                        closure_type
                        init_closure_args...
                    ]
                    convert_assignment(ctx, [K"=" func_name closure_val])
                    ::K"TOMBSTONE"
                ]
            else
                @ast ctx ex (::K"TOMBSTONE")
            end
        else
            # Single-arg K"method" has the side effect of creating a global
            # binding for `func_name` if it doesn't exist.
            @ast ctx ex [K"block"
                [K"method" func_name]
                ::K"TOMBSTONE" # <- function_decl should not be used in value position
            ]
        end
    elseif k == K"method" && kind(ex[1]) === K"BindingId" &&
            haskey(ctx.closure_bindings, ex[1].var_id)
        # rm method table argument if it's a closure id, since it's unnecessary
        # and requires the `(= id (new ...))` call to be lifted above the
        # method.  flisp might be messing up overlays when it does this, since
        # it removes all locals, not just closure ids.
        @ast ctx ex [K"method"
            (::K"nothing"(ex[1]))
            _convert_closures(ctx, ex[2])
            _convert_closures(ctx, ex[3])]
    elseif k == K"function_type"
        func_name = ex[1]
        if kind(func_name) == K"BindingId" && get_binding(ctx, func_name).kind === :local
            @jl_assert(haskey(ctx.closure_infos, func_name.var_id),
                       (ex, "function_type of local without known closure type"))
            ctx.closure_infos[func_name.var_id].type_name
        else
            @ast ctx ex [K"call" "TypeEqOf"::K"core" _convert_closures(ctx, func_name)]
        end
    elseif k == K"method_defs"
        name = ex[1]
        is_closure = kind(name) == K"BindingId" && get_binding(ctx, name).kind === :local
        cap_rewrite = is_closure ? ctx.closure_infos[name.var_id] : nothing
        body_in = ex[2]
        if is_closure
            sig_sparams = ctx.closure_bindings[name.var_id].sig_sparams
            if !isempty(sig_sparams)
                body_in = convert_closure_sig_sparams(ctx, body_in, name.var_id,
                                                      sig_sparams)
            end
        end
        ctx2 = ClosureConversionCtx(ctx.graph, ctx.bindings, ctx.mod,
                                    ctx.closure_bindings, cap_rewrite, ex.lambda_bindings,
                                    ctx.is_toplevel_seq_point, ctx.toplevel_pure, ctx.toplevel_stmts,
                                    ctx.closure_infos)
        body = map_cl_convert(ctx2, body_in, false)
        if is_closure
            if ctx.is_toplevel_seq_point
                body
            else
                # Move methods out to a top-level sequence point.
                push!(ctx.toplevel_stmts, body)
                @ast ctx ex (::K"TOMBSTONE")
            end
        else
            @ast ctx ex [K"block"
                body
                ::K"TOMBSTONE"
            ]
        end
    elseif k == K"_opaque_closure"
        closure_binds = ctx.closure_bindings[ex[1].var_id]
        field_syms, field_orig_bindings, field_inds, _field_is_box =
            closure_type_fields(ctx, ex, closure_binds, true)

        capture_rewrites = ClosureInfo(ex #=unused=#, field_syms, field_inds)

        ctx2 = ClosureConversionCtx(ctx.graph, ctx.bindings, ctx.mod,
                                    ctx.closure_bindings, capture_rewrites, ctx.lambda_bindings,
                                    false, ctx.toplevel_pure, ctx.toplevel_stmts, ctx.closure_infos)

        argt = _convert_closures(ctx, ex[2])
        rt_lb = _convert_closures(ctx, ex[3])
        rt_ub = _convert_closures(ctx, ex[4])

        init_closure_args = SyntaxList(ctx)
        for id in field_orig_bindings
            init_arg = binding_ex(ctx, id)
            if is_self_captured(ctx, init_arg)
                init_arg = captured_var_access(ctx, init_arg)
            end
            push!(init_closure_args, init_arg)
        end
        @ast ctx ex [K"new_opaque_closure"
            argt # arg type tuple
            rt_lb # return_lower_bound
            rt_ub # return_upper_bound
            ex[5] # allow_partial
            [K"opaque_closure_method"
                (::K"nothing")
                ex[6] # nargs
                ex[7] # is_va
                ex[8] # functionloc
                closure_convert_lambda(ctx2, ex[9])
            ]
            init_closure_args...
        ]
    else
        # A small number of kinds are toplevel-preserving in terms of closure
        # closure definitions will be lifted out into `toplevel_stmts` if they
        # occur inside `ex`.
        toplevel_seq_preserving = k == K"if" || k == K"elseif" || k == K"block" ||
                              k == K"tryfinally" || k == K"trycatchelse"
        map_cl_convert(ctx, ex, toplevel_seq_preserving)
    end
end

function closure_convert_lambda(ctx, ex)
    @jl_assert kind(ex) == K"lambda" ex
    lambda_bindings = ex.lambda_bindings
    interpolations = nothing
    if isnothing(ctx.capture_rewriting)
        # Global method which may capture locals
        interpolations = SyntaxList(ctx)
        cap_rewrite = interpolations
    else
        cap_rewrite = ctx.capture_rewriting
    end
    ctx2 = ClosureConversionCtx(ctx.graph, ctx.bindings, ctx.mod,
                                ctx.closure_bindings, cap_rewrite, lambda_bindings,
                                ex.is_toplevel_thunk, ctx.toplevel_pure && ex.toplevel_pure,
                                ctx.toplevel_stmts, ctx.closure_infos)
    lambda_children = SyntaxList(ctx)
    args = ex[1]
    push!(lambda_children, args)
    push!(lambda_children, ex[2])

    # Add box initializations for arguments which are captured by an inner lambda
    body_stmts = SyntaxList(ctx)
    for arg in children(args)
        kind(arg) != K"Placeholder" || continue
        if is_boxed(ctx, arg)
            push!(body_stmts, @ast ctx arg [K"="
                arg
                [K"call" "Box"::K"core" arg]
            ])
        end
    end
    # Convert body.
    input_body_stmts = kind(ex[3]) != K"block" ? ex[3:3] : ex[3][1:end]
    for e in input_body_stmts
        push!(body_stmts, _convert_closures(ctx2, e))
    end
    push!(lambda_children, @ast ctx2 ex[3] [K"block" body_stmts...])

    if numchildren(ex) > 3
        # Convert return type
        @jl_assert numchildren(ex) == 4 ex
        push!(lambda_children, _convert_closures(ctx2, ex[4]))
    end

    lam = setattr!(mknode(ex, lambda_children), :lambda_bindings, lambda_bindings)
    if !isnothing(interpolations) && !isempty(interpolations)
        @ast ctx ex [K"call"
            replace_captured_locals!::K"Value"
            lam
            [K"call"
                "svec"::K"core"
                interpolations...
            ]
        ]
    else
        lam
    end
end


"""
Closure conversion and lowering of bindings

This pass does a few things:
* Deal with typed variables (K"decl") and their assignments
* Deal with const and non-const global assignments
* Convert closures into types
* Lower variables captured by closures into boxes, etc, as necessary

Invariants:
* This pass must not introduce new K"Identifier" - only K"BindingId".
* Any new binding IDs must be added to the enclosing lambda locals
"""
@fzone "JL: closures" function convert_closures(
    ctx::VariableAnalysisContext, ex::SyntaxTree{Attrs}
) where Attrs
    # TODO: ctx.mod is used instead of syntax_module(ex) beyond this point,
    # which is dubious
    ctx_out = ClosureConversionCtx(ctx.graph, ctx.bindings,
                                   ctx.layer.mod,
                                   ctx.closure_bindings, nothing,
                                   ex.lambda_bindings,
                                   false, true, SyntaxList(ctx.graph),
                                   Dict{IdTag,ClosureInfo{Attrs}}())
    ex_out = closure_convert_lambda(ctx_out, ex)
    if !isempty(ctx_out.toplevel_stmts)
        throw(LoweringError(first(ctx_out.toplevel_stmts), "Top level code was found outside any top level context. `@generated` functions may not contain closures, including `do` syntax and generators/comprehension"))
    end
    ctx_out, flatten_blocks(ex_out)
end
