# This file is a part of Julia. License is MIT: https://julialang.org/license

# Package-type analysis is intentionally expressed over root-module identity.
# In particular, these formulas are not reduced with the requires relation:
# ownership portions such as `P & A & B` remain distinct from `P` even when the
# current requires graph makes the two formulas operationally equivalent.
#
# Productivity is represented by the package-type bounds themselves. Bottom
# means that there are no productive witnesses; covariant unions join bottom
# away, while exact components meet with bottom and are annihilated. Nominal
# support includes every instantiated supertype before `Any`, preserving
# `packagetype(S) <= packagetype(T)` whenever `S <: T` without consulting the
# requires graph.
#
# Exact unions require a representation-stability proof. We first discard arms
# proved to be subsumed by the complete remainder (including UnionAll families
# such as JuliaLang/julia#62189). The remaining arm contributions are met only
# when independently closed intersections prove them orthogonal and no outer
# type-variable assignment can erase an arm. Overlapping arms are bounded by
# the meet and join of their possible contributions and delegated to the
# residual hook below. The initial residual hook deliberately returns unknown.

"""
    PackageTypePortion(factors)

One conjunction of root modules in a [`PackageType`](@ref). Factors compare by
module identity.
"""
struct PackageTypePortion
    factors::Vector{Module}
end

"""
    PackageType(alternatives)

A package-ownership formula in disjunctive normal form. Each alternative is a
[`PackageTypePortion`](@ref). An empty alternative list is bottom (there are no
productive witnesses); one alternative with no factors is top (no package is
required).
"""
struct PackageType
    alternatives::Vector{PackageTypePortion}
end

struct PackagetypeDiagnostic
    code::Symbol
    subject::Any
    message::String
end

abstract type AbstractPackagetypeResult end

struct PackagetypeExact <: AbstractPackagetypeResult
    value::PackageType
end

struct PackagetypeUnknown <: AbstractPackagetypeResult
    lower::PackageType
    upper::PackageType
    diagnostics::Vector{PackagetypeDiagnostic}
end

ispackagetypeexact(::PackagetypeExact) = true
ispackagetypeexact(::PackagetypeUnknown) = false

function show(io::IO, portion::PackageTypePortion)
    if isempty(portion.factors)
        print(io, '⊤')
        return
    end
    for (i, factor) in pairs(portion.factors)
        i == 1 || print(io, " & ")
        print(io, nameof(factor))
    end
end

function show(io::IO, package_type::PackageType)
    if isempty(package_type.alternatives)
        print(io, "PackageType(⊥)")
        return
    end
    print(io, "PackageType(")
    for (i, alternative) in pairs(package_type.alternatives)
        i == 1 || print(io, " ∪ ")
        show(io, alternative)
    end
    print(io, ')')
end

function show(io::IO, result::PackagetypeExact)
    print(io, "PackagetypeExact(")
    show(io, result.value)
    print(io, ')')
end

function show(io::IO, result::PackagetypeUnknown)
    print(io, "PackagetypeUnknown(lower=")
    show(io, result.lower)
    print(io, ", upper=")
    show(io, result.upper)
    print(io, ", diagnostics=", length(result.diagnostics), ')')
end

@inline _packagetype_bottom() = PackageType(PackageTypePortion[])
@inline _packagetype_top() = PackageType(PackageTypePortion[PackageTypePortion(Module[])])

@inline function _packagetype_factor_module(mod::Module)
    root = moduleroot(mod)
    return root === Core ? Base : root
end

@inline function _module_in_factors(mod::Module, factors::Vector{Module})
    return any(factor -> factor === mod, factors)
end

function _normalize_package_type_portion(portion::PackageTypePortion)
    factors = Module[]
    for factor in portion.factors
        factor = _packagetype_factor_module(factor)
        _module_in_factors(factor, factors) || push!(factors, factor)
    end
    return PackageTypePortion(factors)
end

# Whether every factor in `a` occurs in `b`.
function _packagetype_portion_subset(a::PackageTypePortion,
                                     b::PackageTypePortion)
    return all(factor -> _module_in_factors(factor, b.factors), a.factors)
end

function _normalize_package_type(alternatives::Vector{PackageTypePortion})
    normalized = PackageTypePortion[]
    for alternative in alternatives
        push!(normalized, _normalize_package_type_portion(alternative))
    end

    # In a positive DNF formula, `A` absorbs `A & B`. Equal portions retain the
    # first occurrence. No requires-graph relation participates in this step.
    keep = trues(length(normalized))
    for i in eachindex(normalized)
        keep[i] || continue
        for j in eachindex(normalized)
            i == j && continue
            keep[j] || continue
            _packagetype_portion_subset(normalized[j], normalized[i]) || continue
            if !_packagetype_portion_subset(normalized[i], normalized[j]) || j < i
                keep[i] = false
                break
            end
        end
    end
    return PackageType(PackageTypePortion[
        normalized[i] for i in eachindex(normalized) if keep[i]
    ])
end

function _packagetype_atom(mod::Module)
    factor = _packagetype_factor_module(mod)
    return PackageType(PackageTypePortion[PackageTypePortion(Module[factor])])
end

# DNF implication. A conjunction `a` implies a conjunction `b` when `b`'s
# factors are a subset of `a`'s factors.
function _packagetype_leq(a::PackageType, b::PackageType)
    for aa in a.alternatives
        any(bb -> _packagetype_portion_subset(bb, aa), b.alternatives) || return false
    end
    return true
end

@inline _packagetype_equiv(a::PackageType, b::PackageType) =
    _packagetype_leq(a, b) && _packagetype_leq(b, a)

function _packagetype_meet(a::PackageType, b::PackageType)
    alternatives = PackageTypePortion[]
    for aa in a.alternatives, bb in b.alternatives
        push!(alternatives, PackageTypePortion(Module[aa.factors..., bb.factors...]))
    end
    return _normalize_package_type(alternatives)
end

function _packagetype_join(a::PackageType, b::PackageType)
    return _normalize_package_type(PackageTypePortion[
        a.alternatives...
        b.alternatives...
    ])
end

@inline _packagetype_lower(result::PackagetypeExact) = result.value
@inline _packagetype_lower(result::PackagetypeUnknown) = result.lower
@inline _packagetype_upper(result::PackagetypeExact) = result.value
@inline _packagetype_upper(result::PackagetypeUnknown) = result.upper
@inline _packagetype_diagnostics(::PackagetypeExact) = PackagetypeDiagnostic[]
@inline _packagetype_diagnostics(result::PackagetypeUnknown) = result.diagnostics

function _packagetype_result(lower::PackageType, upper::PackageType,
                             diagnostics::Vector{PackagetypeDiagnostic})
    @assert _packagetype_leq(lower, upper)
    if _packagetype_equiv(lower, upper)
        return PackagetypeExact(lower)
    end
    return PackagetypeUnknown(lower, upper, diagnostics)
end

function _packagetype_unknown(@nospecialize(subject), code::Symbol, message::String)
    diagnostic = PackagetypeDiagnostic(code, subject, message)
    return PackagetypeUnknown(
        _packagetype_bottom(), _packagetype_top(), PackagetypeDiagnostic[diagnostic])
end

function _packagetype_meet_result(a::AbstractPackagetypeResult,
                                  b::AbstractPackagetypeResult)
    lower = _packagetype_meet(_packagetype_lower(a), _packagetype_lower(b))
    upper = _packagetype_meet(_packagetype_upper(a), _packagetype_upper(b))
    diagnostics = PackagetypeDiagnostic[
        _packagetype_diagnostics(a)...
        _packagetype_diagnostics(b)...
    ]
    return _packagetype_result(lower, upper, diagnostics)
end

function _packagetype_join_result(a::AbstractPackagetypeResult,
                                  b::AbstractPackagetypeResult)
    lower = _packagetype_join(_packagetype_lower(a), _packagetype_lower(b))
    upper = _packagetype_join(_packagetype_upper(a), _packagetype_upper(b))
    diagnostics = PackagetypeDiagnostic[
        _packagetype_diagnostics(a)...
        _packagetype_diagnostics(b)...
    ]
    return _packagetype_result(lower, upper, diagnostics)
end

@inline _packagetype_exact_bottom() = PackagetypeExact(_packagetype_bottom())
@inline _packagetype_exact_top() = PackagetypeExact(_packagetype_top())

@inline _packagetype_is_type_parameter(@nospecialize(parameter)) =
    parameter isa Type || parameter isa TypeVar

function _packagetype_rewrap_local_typevars(@nospecialize(type),
                                            local_typevars::Vector{TypeVar})
    has_free_typevars(type) || return type
    free = find_free_typevars(type)
    for i in length(local_typevars):-1:1
        var = local_typevars[i]
        any(candidate -> candidate === var, free) || continue
        type = UnionAll(var, type)
    end
    return type
end

function _packagetype_make_union(types::Vector{Any})
    isempty(types) && return Bottom
    union_type = types[1]
    for i in 2:length(types)
        union_type = Union{union_type, types[i]}
    end
    return union_type
end

function _packagetype_exact_union_arms(union_type::Union,
                                       local_typevars::Vector{TypeVar})
    arms = Any[
        _packagetype_rewrap_local_typevars(arm, local_typevars)
        for arm in uniontypes(union_type)
    ]

    # Remove one semantically subsumed arm at a time. Iteration is important:
    # equivalent arms must not all be removed simultaneously.
    changed = true
    while changed && length(arms) > 1
        changed = false
        for i in eachindex(arms)
            arm = arms[i]
            has_free_typevars(arm) && continue
            remainder = _packagetype_make_union(Any[
                arms[j] for j in eachindex(arms) if j != i
            ])
            has_free_typevars(remainder) && continue
            if _packagetype_proven_subtype(arm, remainder)
                deleteat!(arms, i)
                changed = true
                break
            end
        end
    end
    return arms
end

# Guard the known intentionally-broken kind-type subtype answers in the same
# manner as Compiler.isnotbrokensubtype.
@inline function _packagetype_proven_subtype(@nospecialize(a), @nospecialize(b))
    a <: b || return false
    return !iskindtype(b) || !isType(a) || b <: a
end

function _packagetype_independent_closure(@nospecialize(type))
    return has_free_typevars(type) ? rewrap_free_typevars(type) : type
end

function _packagetype_proven_orthogonal(@nospecialize(a), @nospecialize(b))
    a = _packagetype_independent_closure(a)
    b = _packagetype_independent_closure(b)
    return typeintersect(a, b) === Bottom
end

# This mirrors the representation-stability distinction made by
# `typeeq_bottomable` in subtype.c. A local unpinned UnionAll variable does not
# make its arm disappear; a free outer variable with a bottom lower bound can.
function _packagetype_union_arm_bottomable(@nospecialize(type),
                                           env::IdDict{TypeVar,Bool}=IdDict{TypeVar,Bool}())
    type === Bottom && return true
    if type isa TypeVar
        if haskey(env, type)
            return env[type] && _packagetype_union_arm_bottomable(type.lb, env)
        end
        return type.lb === Bottom || type.lb isa TypeVar
    elseif type isa Union
        return _packagetype_union_arm_bottomable(type.a, env) &&
               _packagetype_union_arm_bottomable(type.b, env)
    elseif type isa UnionAll
        env[type.var] = type.var.lb === type.var.ub
        result = _packagetype_union_arm_bottomable(type.body, env)
        delete!(env, type.var)
        return result
    elseif type isa DataType && type.name === typename(Tuple)
        for parameter in type.parameters
            isvarargtype(parameter) && continue
            _packagetype_union_arm_bottomable(parameter, env) && return true
        end
    end
    return false
end

"""
    _packagetype_overlapping_union_residual(arm, remainder)

Return `true` after proving that `arm` has a non-bottom residual outside
`remainder`, `false` after proving that it is subsumed, and `nothing` when the
query is unknown. The initial implementation handles complete subsumption
before calling this hook and leaves overlapping residual construction for a
future subtype-aware implementation.
"""
function _packagetype_overlapping_union_residual(@nospecialize(arm),
                                                 @nospecialize(remainder))
    return nothing
end

function _packagetype_analyze_union_covariant(union_type::Union,
                                              local_typevars::Vector{TypeVar})
    result = _packagetype_exact_bottom()
    for arm in uniontypes(union_type)
        arm = _packagetype_rewrap_local_typevars(arm, local_typevars)
        result = _packagetype_join_result(
            result, _packagetype_analyze(arm, false, TypeVar[]))
    end
    return result
end

function _packagetype_exact_union_unknown(arms::Vector{Any},
                                          arm_results::Vector{AbstractPackagetypeResult},
                                          diagnostics::Vector{PackagetypeDiagnostic})
    lower = _packagetype_top()
    upper = _packagetype_bottom()
    for result in arm_results
        lower = _packagetype_meet(lower, _packagetype_lower(result))
        upper = _packagetype_join(upper, _packagetype_upper(result))
        append!(diagnostics, _packagetype_diagnostics(result))
    end
    push!(diagnostics, PackagetypeDiagnostic(
        :overlapping_exact_union,
        _packagetype_make_union(arms),
        "could not prove a stable residual for every overlapping union arm"))
    return _packagetype_result(lower, upper, diagnostics)
end

function _packagetype_analyze_union_exact(union_type::Union,
                                          local_typevars::Vector{TypeVar})
    arms = _packagetype_exact_union_arms(union_type, local_typevars)

    isempty(arms) && return _packagetype_exact_bottom()
    if length(arms) == 1
        return _packagetype_analyze(arms[1], true, TypeVar[])
    end

    arm_results = AbstractPackagetypeResult[
        _packagetype_analyze(arm, true, TypeVar[]) for arm in arms
    ]

    bottomable = any(_packagetype_union_arm_bottomable, arms)
    pairwise_orthogonal = true
    for i in eachindex(arms), j in 1:i-1
        if !_packagetype_proven_orthogonal(arms[i], arms[j])
            pairwise_orthogonal = false
            break
        end
    end

    stable = pairwise_orthogonal && !bottomable
    if !stable && !bottomable
        stable = true
        for i in eachindex(arms)
            remainder = _packagetype_make_union(Any[
                arms[j] for j in eachindex(arms) if j != i
            ])
            residual = _packagetype_overlapping_union_residual(arms[i], remainder)
            if residual !== true
                stable = false
                break
            end
        end
    end

    if stable
        result = _packagetype_exact_top()
        for arm_result in arm_results
            result = _packagetype_meet_result(result, arm_result)
        end
        return result
    end

    diagnostics = PackagetypeDiagnostic[]
    if bottomable
        push!(diagnostics, PackagetypeDiagnostic(
            :bottomable_exact_union_arm,
            union_type,
            "an outer type-variable assignment may remove a union arm"))
    end
    return _packagetype_exact_union_unknown(arms, arm_results, diagnostics)
end

function _packagetype_analyze_unionall(unionall::UnionAll, exact::Bool,
                                       local_typevars::Vector{TypeVar})
    var = unionall.var
    if has_free_typevars(var.lb) || has_free_typevars(var.ub)
        return _packagetype_unknown(unionall, :dependent_unionall_bound,
            "dependent UnionAll bounds are not implemented")
    end
    push!(local_typevars, var)
    result = _packagetype_analyze(unionall.body, exact, local_typevars)
    pop!(local_typevars)
    return result
end

function _packagetype_analyze_typevar(var::TypeVar, exact::Bool)
    var.ub === Bottom && return _packagetype_exact_bottom()
    if has_free_typevars(var.lb) || has_free_typevars(var.ub)
        return _packagetype_unknown(var, :dependent_typevar_bound,
            "dependent TypeVar bounds are not implemented")
    end
    # An unpinned variable ranges over productive subtypes of its upper bound.
    # A lower bound alone cannot establish a package requirement.
    bound_exact = exact && var.lb === var.ub
    return _packagetype_analyze(var.ub, bound_exact, TypeVar[])
end

function _packagetype_analyze_vararg(vararg::Core.TypeofVararg,
                                     has_fixed_prefix::Bool,
                                     local_typevars::Vector{TypeVar})
    if isdefined(vararg, :N)
        count = vararg.N
        count === 0 && return _packagetype_exact_top()
        count isa Int || return _packagetype_unknown(vararg, :variable_vararg_length,
            "a variable Vararg length is not implemented")
    elseif has_fixed_prefix
        # The zero-length tail is a productive witness that does not require
        # anything from the repeated element type.
        return _packagetype_exact_top()
    end
    return _packagetype_analyze(vararg.T, false, local_typevars)
end

function _packagetype_analyze_tuple(tuple_type::DataType,
                                    local_typevars::Vector{TypeVar})
    result = PackagetypeExact(_packagetype_atom(tuple_type.name.module))
    isempty(tuple_type.parameters) && return _packagetype_exact_bottom()
    has_fixed_prefix = false
    for parameter in tuple_type.parameters
        if isvarargtype(parameter)
            parameter_result = _packagetype_analyze_vararg(
                unwrap_unionall(parameter), has_fixed_prefix, local_typevars)
        else
            has_fixed_prefix = true
            parameter_result = _packagetype_analyze(
                parameter, false, local_typevars)
        end
        result = _packagetype_meet_result(result, parameter_result)
    end
    return result
end

function _packagetype_analyze_datatype(datatype::DataType,
                                       local_typevars::Vector{TypeVar})
    datatype.name === typename(Tuple) &&
        return _packagetype_analyze_tuple(datatype, local_typevars)

    result = PackagetypeExact(_packagetype_atom(datatype.name.module))
    for parameter in datatype.parameters
        _packagetype_is_type_parameter(parameter) || continue
        parameter_result = _packagetype_analyze(
            parameter, true, local_typevars)
        result = _packagetype_meet_result(result, parameter_result)
    end

    if datatype !== Any
        super = supertype(datatype)
        if super !== Any
            super_result = _packagetype_analyze(
                super, true, local_typevars)
            result = _packagetype_meet_result(result, super_result)
        end
    end
    return result
end

function _packagetype_analyze(@nospecialize(type), exact::Bool,
                              local_typevars::Vector{TypeVar})
    type === Bottom && return _packagetype_exact_bottom()
    if type isa Union
        return exact ?
            _packagetype_analyze_union_exact(type, local_typevars) :
            _packagetype_analyze_union_covariant(type, local_typevars)
    elseif type isa UnionAll
        return _packagetype_analyze_unionall(type, exact, local_typevars)
    elseif type isa TypeVar
        return _packagetype_analyze_typevar(type, exact)
    elseif isType(type)
        base = PackagetypeExact(_packagetype_atom(typename(Core.Type).module))
        parameter = _packagetype_analyze(
            type_parameter(type), true, local_typevars)
        return _packagetype_meet_result(base, parameter)
    elseif type isa DataType
        return _packagetype_analyze_datatype(type, local_typevars)
    end
    return _packagetype_unknown(type, :unsupported_type_form,
        "the type form is not implemented by package-type analysis")
end

"""
    packagetype(T::Type) -> AbstractPackagetypeResult

Compute the package-ownership formula shared by the productive closed subtypes
of `T`. The result is [`PackagetypeExact`](@ref) only when both conservative
bounds coincide. Unsupported or representation-unstable cases return
[`PackagetypeUnknown`](@ref); an unknown result grants no type-derived
ownership authority. A non-bottom lower bound is also a conservative proof
that `T` has productive support.
"""
function packagetype(@nospecialize(type::Type))
    return _packagetype_analyze(type, false, TypeVar[])
end
