# Type-piracy detection.
#
# `moduletype(T)` computes the set of *root modules* whose TypeNames are
# unavoidable in any admissible subtype witness of the type expression `T`
# (see the design notes). A method definition is *not* piracy iff the defining
# package's root module is among `moduletype(sig)` of the method's signature
# tuple — equivalently, the package owns the function (the `typeof(f)` element of
# the signature) or one of the genuinely-required argument types.
#
# This is the SOUND ("never miss piracy") direction: `moduletype` UNDER-
# approximates the true required set, so any approximation can only over-flag a
# legitimate method, never clear a real pirate.
#
# `check_method(m)` is the verifier the runtime calls directly from `jl_method_def`
# (registered via `jl_set_methoddef_verifier`, see `src/gf.c`); it is installed by
# default in `activate_codegen!` and can be toggled with `enable!()`/`disable!()`.
#
# kwarg methods: a `kwcall` method's signature is
#   `Tuple{typeof(Core.kwcall), NamedTuple, typeof(f), positional...}`
# so the function's owner is carried in slot 3 and the positional args in slots
# 4+; the keyword *types* never appear (they aren't dispatched on). No special
# handling is required — `moduletype` reasons about it precisely as-is.
module TypePiracy

using Base
# `Set` (base/set.jl) is not yet loaded when the Compiler bootstraps, but `IdSet`
# (and the AbstractSet ops) are — and identity is the right comparison for
# `Module`s anyway, so we use `IdSet{Module}` throughout.
using Base: moduleroot, uniontypes, rewrap_free_typevars, typeintersect_env, IdSet,
    unwrap_unionall, argument_datatype, isType

# ---------------------------------------------------------------------------
# module accounting
# ---------------------------------------------------------------------------
typename_module(tn::Core.TypeName) = moduleroot(tn.module)

# {M : head/supertype chain of T touches M}, collected into `acc`.
function chain_modules!(acc::IdSet{Module}, @nospecialize(T::DataType))
    S = T
    while true
        push!(acc, typename_module(S.name))
        sup = supertype(S); sup === S && break; S = sup
    end
    return acc
end
function head_forces_module(@nospecialize(T::DataType), M::Module)
    S = T
    while true
        typename_module(S.name) === M && return true
        sup = supertype(S); sup === S && break; S = sup
    end
    return false
end

# {M : T uses M} — equal, by construction, to `candidate_modules(T)`.
function uses_module(@nospecialize(T), M::Module)
    if T isa Union
        return uses_module(T.a, M) || uses_module(T.b, M)
    elseif T isa UnionAll
        return uses_module(T.var.ub, M) || uses_module(T.var.lb, M) || uses_module(T.body, M)
    elseif T isa TypeVar
        return uses_module(T.ub, M) || uses_module(T.lb, M)
    elseif T isa DataType
        T === Union{} && return false
        head_forces_module(T, M) && return true
        for p in T.parameters; uses_module(p, M) && return true; end
        return false
    elseif T isa Core.TypeofVararg
        (isdefined(T, :T) && uses_module(T.T, M)) && return true
        (isdefined(T, :N) && uses_module(T.N, M)) && return true
        return false
    else
        return false
    end
end

function candidate_modules(@nospecialize(T), acc::IdSet{Module}=IdSet{Module}())
    if T isa Union
        candidate_modules(T.a, acc); candidate_modules(T.b, acc)
    elseif T isa UnionAll
        candidate_modules(T.var.ub, acc); candidate_modules(T.var.lb, acc); candidate_modules(T.body, acc)
    elseif T isa TypeVar
        candidate_modules(T.ub, acc); candidate_modules(T.lb, acc)
    elseif T isa DataType
        T === Union{} && return acc
        chain_modules!(acc, T)
        for p in T.parameters; candidate_modules(p, acc); end
    elseif T isa Core.TypeofVararg
        isdefined(T, :T) && candidate_modules(T.T, acc)
        isdefined(T, :N) && candidate_modules(T.N, acc)
    end
    return acc
end

# ---------------------------------------------------------------------------
# disjointness ("undroppable") via typeintersect + forbid-bottom readback
# ---------------------------------------------------------------------------
# `Ai` cannot be absorbed into `S` with a NON-BOTTOM instantiation iff they are
# disjoint, or the only intersection pins an (implicit-`Union{}`) binder to ⊥.
function undroppable(@nospecialize(Ai), @nospecialize(S), strict_bottom::Bool)
    a = rewrap_free_typevars(Ai)
    for (x, y) in ((a, S), (S, a))
        r = typeintersect_env(x, y)          # Pair{Any, SimpleVector}
        r.first === Union{} && return true   # disjoint
        # Without strict-bottom, an intersection that only succeeds by pinning a
        # binder to ⊥ is inadmissible ⇒ no (non-bottom) overlap. Without it, ⊥ is
        # a real value, so such an intersection IS an overlap (don't bail here).
        !strict_bottom && env_has_forced_bottom(r.second) && return true
    end
    return false
end
function env_has_forced_bottom(env::Core.SimpleVector)
    for e in env
        v = (e isa Core.SimpleVector && length(e) == 2) ? e[1] : e
        v === Union{} && return true
        (v isa TypeVar && v.ub === Union{}) && return true
    end
    return false
end

# ---------------------------------------------------------------------------
# the SET-valued required predicate (mirrors moduletype_requires.jl pointwise)
# `U` is the candidate universe, threaded for the ⊥-pinned typevar edge case.
# ---------------------------------------------------------------------------
function required_cov(@nospecialize(T), U::IdSet{Module}, strict_bottom::Bool)
    if T === Union{}
        return IdSet{Module}()
    elseif T isa Union                               # covariant: required iff EVERY arm is ⇒ ∩
        return intersect(required_cov(T.a, U, strict_bottom), required_cov(T.b, U, strict_bottom))
    elseif T isa UnionAll
        return required_cov(T.body, U, strict_bottom)
    elseif T isa TypeVar
        return required_tvar(T.lb, T.ub, U, strict_bottom)
    elseif T isa Core.TypeofVararg
        return IdSet{Module}()
    elseif T isa DataType
        return required_datatype(T, U, true, strict_bottom)
    else
        return IdSet{Module}()
    end
end

function required_exact(@nospecialize(T), U::IdSet{Module}, strict_bottom::Bool)
    if T === Union{}
        return IdSet{Module}()
    elseif T isa Union
        return required_union_exact(T, U, strict_bottom)
    elseif T isa UnionAll
        return required_exact(T.body, U, strict_bottom)
    elseif T isa TypeVar
        return required_tvar(T.lb, T.ub, U, strict_bottom)
    elseif T isa Core.TypeofVararg
        return IdSet{Module}()
    elseif T isa DataType
        return required_datatype(T, U, false, strict_bottom)
    else
        return IdSet{Module}()
    end
end

function required_datatype(@nospecialize(T::DataType), U::IdSet{Module}, cov::Bool, strict_bottom::Bool)
    acc = chain_modules!(IdSet{Module}(), T)           # head/supertype chain
    istuple = T.name === Tuple.name
    for p in T.parameters
        if p isa Core.TypeofVararg
            union!(acc, required_vararg(p, U, strict_bottom))
        elseif !(p isa Type) && !(p isa TypeVar)
            # value parameter contributes nothing
        else
            pcov = istuple && cov                    # Tuple params covariant only in cov ctx
            union!(acc, pcov ? required_cov(p, U, strict_bottom) : required_exact(p, U, strict_bottom))
        end
    end
    return acc
end

function required_vararg(@nospecialize(V::Core.TypeofVararg), U::IdSet{Module}, strict_bottom::Bool)
    fixed_positive = isdefined(V, :N) && V.N isa Int && V.N >= 1
    fixed_positive || return IdSet{Module}()           # zero-length ⇒ element not forced
    isdefined(V, :T) || return IdSet{Module}()
    return required_cov(V.T, U, strict_bottom)
end

# A module is required by a typevar bound iff EVERY admissible candidate value
# uses it ⇒ intersection of the candidates' module sets.
function required_tvar(@nospecialize(lb), @nospecialize(ub), U::IdSet{Module}, strict_bottom::Bool)
    # Without strict-bottom, an implicit-⊥ lower bound admits `Union{}`, which uses
    # no module ⇒ the bound can avoid everything ⇒ nothing is required.
    (!strict_bottom && lb === Union{}) && return IdSet{Module}()
    cands = ub isa Union ? Any[ub, uniontypes(ub)...] : Any[ub]
    push!(cands, lb)
    acc = nothing                                    # ⋂ over admissible candidates
    for c in cands
        (c !== Union{} && c isa Type && lb <: c && c <: ub) || continue
        cm = candidate_modules(c)
        acc = acc === nothing ? cm : intersect!(acc::IdSet{Module}, cm)
    end
    acc === nothing && return copy(U)                # ⊥-pinned ⇒ requires everything
    return acc::IdSet{Module}
end

# Exact union: ⋃ᵢ ⋂_{j : overlap(Aᵢ,Aⱼ)} required(Aⱼ). `overlap = !undroppable`
# is module-independent, so it is computed once (O(n²)).
function required_union_exact(@nospecialize(Uty::Union), U::IdSet{Module}, strict_bottom::Bool)
    arms = uniontypes(Uty)                           # already a Vector
    n = length(arms)
    arm_sets = [required_exact(a, U, strict_bottom) for a in arms]
    wrapped  = [rewrap_free_typevars(a) for a in arms]
    result = IdSet{Module}()
    for i in 1:n
        acc = copy(arm_sets[i])                      # arm i overlaps itself
        for j in 1:n
            (j == i || isempty(acc)) && continue
            undroppable(arms[i], wrapped[j], strict_bottom) || intersect!(acc, arm_sets[j])
        end
        union!(result, acc)
    end
    return result
end

# ---------------------------------------------------------------------------
"""
    witness_avoiding(T, M) -> (W::Type or nothing)

A single concrete `M`-free witness `W <: T` proving `M` is avoidable — a
counterexample that names no type from module `M` — or `nothing` if none can be
exhibited here. Computed on demand for the *specific* `M` under test (typically
an avoidable module of `moduletype(T)`); we only ever need one. Covariant: it
threads through `Union` arms and `Tuple` parameters.
"""
function witness_avoiding(@nospecialize(T), M::Module)
    if !uses_module(T, M)
        return T
    elseif T isa Union
        for a in (T.a, T.b)
            w = witness_avoiding(a, M); w === nothing || return w
        end
        return nothing
    elseif T isa UnionAll
        w = witness_avoiding(T.body, M)
        return w === nothing ? nothing : rewrap_free_typevars(w)
    elseif T isa DataType && T.name === Tuple.name
        ws = Any[]
        for p in T.parameters
            if p isa Core.TypeofVararg
                if isdefined(p, :N) && p.N isa Int && p.N >= 1
                    isdefined(p, :T) || return nothing
                    w = witness_avoiding(p.T, M); w === nothing && return nothing
                    push!(ws, Vararg{w, p.N})
                end
            else
                w = witness_avoiding(p, M); w === nothing && return nothing
                push!(ws, w)
            end
        end
        return Tuple{ws...}
    else
        return nothing
    end
end

# ---------------------------------------------------------------------------
# top level
# ---------------------------------------------------------------------------
"""
    moduletype(T; strict_bottom::Bool=true) -> IdSet{Module}

The set of root modules PROVED necessary in any subtype witness of `T` — the
conjunction of owners. Sound for piracy: a subset of the true required set, so a
module's absence is a real "avoidable" (never a false avoidable).

`strict_bottom` (default `true`) treats an implicit-`Union{}` lower-bound `TypeVar`
(e.g. `T` in `where T<:Foo`) as *not* instantiable to exactly `Union{}`, so an
intersection that succeeds only by forcing such a var to `Union{}` is ignored.
Set it `false` to recover Julia's current "`Union{}` is admissible" behavior — a
var that can be `Union{}` then avoids every module, so it requires nothing.

Use [`witness_avoiding`](@ref)`(T, M)` to obtain, on demand, a counterexample for
a *specific* avoidable module `M` (e.g. the one being enforced) — we never need
witnesses for every avoidable module, only one for the module under test.
"""
moduletype(@nospecialize(T); strict_bottom::Bool=false) =
    required_cov(T, candidate_modules(T), strict_bottom)

# ---------------------------------------------------------------------------
# the method-definition hook
# ---------------------------------------------------------------------------
# The module that owns the function `m` extends — derived from the signature the
# same way `jl_method_def` / `Base.show(::Method)` do (`argument_datatype` +
# `isType`, c.f. methodshow.jl), NOT `m.module`, which is where the (potential
# pirate) *method* is defined. A `kwcall` method carries the real callee in slot 3.
function pirated_function_module(m::Method)
    t = unwrap_unionall(m.sig)
    (t isa DataType && !isempty(t.parameters)) || return m.module
    ps = t.parameters
    ftarg = (ps[1] === typeof(Core.kwcall) && length(ps) >= 3) ? ps[3] : ps[1]
    ft = argument_datatype(ftarg)
    isType(ft) && (ft = argument_datatype(ft.parameters[1]))   # constructor: Type{X} → X
    ft === nothing ? m.module : Base.parentmodule(ft)
end

# ---------------------------------------------------------------------------
# precompilation logging
# ---------------------------------------------------------------------------
# Type-piracy warning printing is currently disabled in favour of accumulating
# per-method query data and flushing it as JSON at end of precompilation. The
# log is per-process (each precompile subprocess has its own copy) and is keyed
# by defining root module; one `<RootModule>.json` is written under
# `JULIA_DEBUG_TYPE_PIRACY_DIR` from `compile_and_emit_native` (see precompile.jl).
# When the env var is unset, `check_method` is a near no-op (no `moduletype` work).
const _log = IdDict{Module, Vector{Any}}()

# `sprint(show, x)` is what users would see (overridable). `_raw_str` bypasses
# user `show` overrides by routing the value through `jl_static_show` (the same
# canonical C printer used by `jl_(x)` in gdb). `JL_STREAM` is `uv_stream_t`, so
# we capture by writing into a `Pipe`'s libuv write end and reading the other.
_show_str(@nospecialize x) =
    try sprint(show, x) catch _; "<show failed>" end
function _raw_str(@nospecialize x)
    try
        pipe = Base.Pipe()
        Base.link_pipe!(pipe; reader_supports_async=false, writer_supports_async=false)
        ccall(:jl_static_show, Csize_t, (Ptr{Cvoid}, Any), pipe.in.handle, x)
        close(pipe.in)
        s = read(pipe.out, String)
        close(pipe.out)
        return s
    catch _
        return "<raw failed>"
    end
end

function _record!(m::Method)
    # `Base.ENV` is defined deep in `base/Base.jl` (env.jl), AFTER the world at
    # which `_record!` is loaded/inferred via the verifier's pinned world. Use
    # `getenv` directly to stay world-agnostic. We type the ccall with the Core
    # types `Ptr{UInt8}` (not `Cstring`/`C_NULL`) because those are not yet in
    # `TypePiracy`'s scope at Compiler bootstrap (`UndefVarError(:Cstring)`).
    ccall(:getenv, Ptr{UInt8}, (Ptr{UInt8},), "JULIA_DEBUG_TYPE_PIRACY_DIR") == Ptr{UInt8}() && return nothing
    sig     = m.sig
    fmod    = pirated_function_module(m)
    defroot = moduleroot(m.module)
    results = Any[]
    for strict in (true, false)
        mt = moduletype(sig; strict_bottom=strict)
        is_piracy = !(defroot in mt)
        wit = is_piracy ? witness_avoiding(sig, defroot) : nothing
        push!(results, (strict, sort!(collect(mt); by=string), is_piracy, wit))
    end
    arr = Base.get!(() -> Any[], _log, defroot)
    push!(arr, (fmod, m.name, sig, m.file, m.line, results))
    return nothing
end

# JSON string escape -- mirrors `print_str_escape_json` (src/gc-heap-snapshot.c).
function _print_json_string(io::IO, s::AbstractString)
    print(io, '"')
    for c in s
        if     c == '"';  print(io, "\\\"")
        elseif c == '\\'; print(io, "\\\\")
        elseif c == '\b'; print(io, "\\b")
        elseif c == '\f'; print(io, "\\f")
        elseif c == '\n'; print(io, "\\n")
        elseif c == '\r'; print(io, "\\r")
        elseif c == '\t'; print(io, "\\t")
        elseif c < ' '
            print(io, "\\u", lpad(string(UInt32(c); base=16), 4, '0'))
        else
            print(io, c)
        end
    end
    print(io, '"')
end

# Pretty-printed (2-space indented) JSON. `depth` is the indent level at which
# the object's `{` is rendered; the caller is responsible for the leading indent
# of the open brace, but the closing brace is indented by this function.
function _print_indent(io::IO, depth::Int)
    for _ in 1:depth
        print(io, "  ")
    end
end

function _print_json_entry(io::IO, e, depth::Int)
    (fmod, name, sig, file, line, results) = e
    print(io, "{\n")
    _print_indent(io, depth+1); print(io, "\"function\": ");      _print_json_string(io, string(fmod) * "." * string(name)); print(io, ",\n")
    # _print_indent(io, depth+1); print(io, "\"function_raw\": ");  _print_json_string(io, _raw_str(fmod) * "." * string(name)); print(io, ",\n")
    _print_indent(io, depth+1); print(io, "\"signature\": ");     _print_json_string(io, _show_str(sig)); print(io, ",\n")
    _print_indent(io, depth+1); print(io, "\"signature_raw\": "); _print_json_string(io, _raw_str(sig)); print(io, ",\n")
    _print_indent(io, depth+1); print(io, "\"file\": ");          _print_json_string(io, string(file)); print(io, ",\n")
    _print_indent(io, depth+1); print(io, "\"line\": ", line, ",\n")
    _print_indent(io, depth+1); print(io, "\"results\": ")
    if isempty(results)
        print(io, "[]\n")
    else
        print(io, "[\n")
        for (i, r) in enumerate(results)
            (strict, mt, is_piracy, wit) = r
            _print_indent(io, depth+2); print(io, "{\n")
            _print_indent(io, depth+3); print(io, "\"strict_bottom\": ", strict, ",\n")
            _print_indent(io, depth+3); print(io, "\"moduletype\": [")
            for (j, mod) in enumerate(mt)
                j > 1 && print(io, ", ")
                _print_json_string(io, string(mod))
            end
            print(io, "],\n")
            _print_indent(io, depth+3); print(io, "\"piracy\": ", is_piracy)
            if is_piracy
                print(io, ",\n")
                _print_indent(io, depth+3); print(io, "\"witness\": ")
                wit === nothing ? print(io, "null") : _print_json_string(io, _show_str(wit))
                print(io, ",\n")
                _print_indent(io, depth+3); print(io, "\"witness_raw\": ")
                wit === nothing ? print(io, "null") : _print_json_string(io, _raw_str(wit))
            end
            print(io, "\n")
            _print_indent(io, depth+2); print(io, "}")
            i < length(results) && print(io, ",")
            print(io, "\n")
        end
        _print_indent(io, depth+1); print(io, "]\n")
    end
    _print_indent(io, depth); print(io, "}")
end

"""
    dump_log!()

Flush the accumulated per-method type-piracy query data as one JSON file per
defining root module under `JULIA_DEBUG_TYPE_PIRACY_DIR`. No-op when the env var
is unset or no methods have been recorded. Called from `compile_and_emit_native`
at the end of precompilation (object-file output time).
"""
function dump_log!()
    # `getenv` with Core-only ccall types — see `_record!`.
    ptr = ccall(:getenv, Ptr{UInt8}, (Ptr{UInt8},), "JULIA_DEBUG_TYPE_PIRACY_DIR")
    (ptr == Ptr{UInt8}() || isempty(_log)) && return nothing
    dir = unsafe_string(ptr)
    Base.mkpath(dir)
    for (mod, entries) in _log
        path = Base.joinpath(dir, string(nameof(mod)) * ".json")
        Base.open(path, "w") do io
            if isempty(entries)
                print(io, "[]\n")
            else
                print(io, "[\n")
                for (i, e) in enumerate(entries)
                    _print_indent(io, 1)
                    _print_json_entry(io, e, 1)
                    i < length(entries) && print(io, ",")
                    print(io, "\n")
                end
                print(io, "]\n")
            end
        end
    end
    Base.empty!(_log)
    return nothing
end

"""
    check_method(m::Method)

Record type-piracy query data for `m`. Currently the warning-printing path is
disabled (commented out below); when `JULIA_DEBUG_TYPE_PIRACY_DIR` is set, the
recorded entries are flushed as JSON by `dump_log!` at end of precompilation.
Installed as the `jl_method_def` hook via `enable!`.
"""
function check_method(m::Method)
    _record!(m)
    # ---- warning printing currently disabled; kept for future re-enable ----
    # sig = m.sig
    # defroot = moduleroot(m.module)
    # required = moduletype(sig)
    # (defroot in required) && return nothing          # owns f or a required arg type ⇒ OK
    # # `defroot` is (by definition of piracy) typically absent from `sig`, so the
    # # witness avoiding it is usually `sig` itself — a call matching this method
    # # that names none of the defining package's types. Compute it directly.
    # w = witness_avoiding(sig, defroot)
    # io = Core.stderr
    # print(io, "WARNING: possible type piracy: ", m.module, " extends `",
    #             pirated_function_module(m), ".", m.name, "` at ", m.file, ":", m.line, "\n")
    # print(io, "    signature       : ")
    # ccall(:jl_, Cvoid, (Any,), sig)
    # print(io, "    required owners  : ")
    # first = true
    # for owner in required
    #     !first && print(io, " & ")
    #     print(io, owner)
    #     first = false
    # end
    # print(io, "\n")
    # w === nothing || print(io, "    witness avoiding ", defroot, " : ", w, "\n")
    return nothing
end

# Install/remove `check_method` as THE method-definition verifier (a single
# Compiler-owned entry, called directly by the runtime in its own pinned world —
# not a pluggable hook). The setter captures the current world so `check_method`
# and the `moduletype` methods it calls remain visible from `jl_method_def`.
"Activate type-piracy checking on every subsequent method definition."
enable!()  = (ccall(:jl_set_methoddef_verifier, Cvoid, (Any,), check_method); nothing)
"Deactivate type-piracy checking."
disable!() = (ccall(:jl_set_methoddef_verifier, Cvoid, (Any,), nothing); nothing)

end # module TypePiracy
