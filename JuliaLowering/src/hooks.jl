# TODO: Allow `soft_scope::Union{Nothing,Bool}` to be passed through `jl_lower` C API

"""
Becomes `Core._lower()` upon activating JuliaLowering.

Returns an svec with the lowered code (usually expr) as its first element, and
(until integration is less experimental) whatever we want after it
"""
function core_lowering_hook(@nospecialize(code), mod::Module, file::Union{String,Ptr{UInt8}}="none",
                            line::Integer=0, world::UInt=typemax(Csize_t), _warn::Bool=false)
    if !(code isa SyntaxTree || code isa Expr)
        # e.g. LineNumberNode, integer...
        return Core.svec(code)
    end

    if _has_v1_13_hooks && Core._lower === core_lowering_hook &&
            unsafe_load(cglobal(:jl_lowering_world, Csize_t)) == 0
        # Refuse to run as `Core._lower` without a pinned world
        error("`Core._lower` was set without pinning the lowering world; use `JuliaLowering.activate!()`")
    end

    # TODO: fix in base
    file = file isa Ptr{UInt8} ? unsafe_string(file) : file
    line = !(line isa Int) ? Int(line) : line

    local st0, st1 = nothing, nothing
    try
        st0 = code isa Expr ? expr_to_est(code, LineNumberNode(line, file)) : code
        if kind(st0) in KSet"toplevel module"
            return Core.svec(code)
        elseif kind(st0) === K"doc" && numchildren(st0) >= 2 && kind(st0[2]) === K"module"
            # TODO: this ignores module docstrings for now
            return Core.svec(est_to_expr(st0[2]))
        end
        st0 = rebase_layers(st0, mod, JL_OLD_SYNTAX_VERSION)
        st1 = expand_forms_1(st0, world, true)
        # Re-check the kind after macro/hygiene expansion, mirroring the
        # pre-expansion early-out on `st0` above. `expand_forms_1` can turn a
        # `hygienic-scope`-wrapped form into a bare top-level `module`: a macro
        # returning `Expr(:toplevel, Expr(:module, ...))` (the "macro defines a
        # module" idiom, e.g. EnumX/SuperEnum) that is `@macroexpand`ed and then
        # `eval`ed separately reaches us as the `hygienic-scope`-wrapped `module`
        # child alone -- the C toplevel driver (`jl_eval_toplevel_stmts`) peels
        # the enclosing `:toplevel` and re-lowers each child, and only the
        # `module` child needs lowering. Such a `module` is genuinely top-level,
        # but `expand_forms_2` unconditionally rejects any `module` it sees (at
        # that point one can only be illegally nested). Wrap it in a `toplevel`
        # so it reuses the existing `K"toplevel"` handling, which defers module
        # creation to a fresh `eval` (preserving the body's macro hygiene), just
        # as happens when the same macro is expanded and evaluated in one step.
        if kind(st1) === K"module"
            st1 = @ast st1._graph st1 [K"toplevel" st1]
        end
        ctx2, st2 = expand_forms_2(st1, world)
        ctx3, st3 = resolve_scopes(ctx2, st2)
        ctx4, st4 = convert_closures(ctx3, st3)
        ctx5, st5 = linearize_ir(ctx4, st4)
        ex = to_lowered_expr(st5)
        return Core.svec(ex, st5, ctx5)
    catch exc
        @info("JuliaLowering threw given input:", code=code, st0=st0, st1=st1, file=file, line=line, mod=mod)
        rethrow(exc)

        # TODO: Re-enable flisp fallback once we're done collecting errors
        # @error("JuliaLowering failed — falling back to flisp!",
        #        exception=(exc,catch_backtrace()),
        #        code=code, file=file, line=line, mod=mod)
        # return Base.fl_lower(code, mod, file, line, world, warn)
    end
end

# TODO: Write a parser hook here.  The input to `core_lowering_hook` should
# eventually be a (convertible to) SyntaxTree, but we need to make updates to
# the parsing API to include a parameter for AST type.

const _has_v1_13_hooks = isdefined(Core, :_lower)

function activate!(enable=true)
    if !_has_v1_13_hooks
        error("Cannot use JuliaLowering without `Core._lower` binding or in $VERSION < 1.13")
    end

    if enable
        Core._setlowerer!(core_lowering_hook)
        ccall(:jl_set_lowering_world, Cvoid, (Csize_t,), Base.get_world_counter())
    else
        Core._setlowerer!(Base.fl_lower)
        # Unlike JL, `jl_lower` dispatches the flisp wrapper at the latest world
        ccall(:jl_set_lowering_world, Cvoid, (Csize_t,), 0)
    end
end
