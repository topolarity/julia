# This file is a part of Julia. License is MIT: https://julialang.org/license

# The package-type definitions are loaded into Base after the sysimage Compiler
# during bootstrap. Keep their names qualified and out of method signatures so
# these routines can be defined before Base.packagetype itself is available.

@inline _arg0_package_bottom() = Base._packagetype_bottom()
@inline _arg0_package_top() = Base._packagetype_top()
@inline _arg0_package_atom(mod::Module) = Base._packagetype_atom(mod)

function _arg0_package_join(a, b)
    return Base._packagetype_join(a, b)
end

function _arg0_package_meet(a, b)
    return Base._packagetype_meet(a, b)
end

function _arg0_invariant_union_owner(union_type::Union,
                                     local_typevars::Vector{TypeVar})
    arms = Base._packagetype_exact_union_arms(union_type, local_typevars)
    isempty(arms) && return _arg0_package_atom(Base)
    length(arms) == 1 &&
        return _arg0_invariant_package_owner(arms[1], TypeVar[])

    owners = Any[
        _arg0_invariant_package_owner(arm, TypeVar[]) for arm in arms
    ]
    owner_meet = _arg0_package_top()
    owner_join = _arg0_package_bottom()
    for owner in owners
        owner_meet = _arg0_package_meet(owner_meet, owner)
        owner_join = _arg0_package_join(owner_join, owner)
    end

    # If every possible surviving arm has the same owner formula, unstable
    # normalization cannot affect the answer.
    Base._packagetype_equiv(owner_meet, owner_join) && return owner_meet

    any(Base._packagetype_union_arm_bottomable, arms) &&
        return _arg0_package_top()
    pairwise_orthogonal = true
    for i in eachindex(arms), j in 1:i-1
        if !Base._packagetype_proven_orthogonal(arms[i], arms[j])
            pairwise_orthogonal = false
            break
        end
    end
    if !pairwise_orthogonal
        for i in eachindex(arms)
            remainder = Base._packagetype_make_union(Any[
                arms[j] for j in eachindex(arms) if j != i
            ])
            Base._packagetype_overlapping_union_residual(
                arms[i], remainder) === true || return _arg0_package_top()
        end
    end
    return owner_meet
end

function _arg0_invariant_package_owner(@nospecialize(type),
                                       local_typevars::Vector{TypeVar})
    type === Bottom && return _arg0_package_atom(Base)
    if type isa Union
        return _arg0_invariant_union_owner(type, local_typevars)
    elseif type isa UnionAll
        push!(local_typevars, type.var)
        owner = _arg0_invariant_package_owner(type.body, local_typevars)
        pop!(local_typevars)
        return owner
    elseif type isa TypeVar
        type.lb === type.ub || return _arg0_package_top()
        return _arg0_invariant_package_owner(type.ub, local_typevars)
    elseif type isa DataType
        return _arg0_package_atom(type.name.module)
    end
    return _arg0_package_top()
end

"""
    arg0_invariant_package_owner(T)

Return the package formula which owns dispatch on the exact type object `T`,
as used by constructor-like `Type{T}` call signatures. Ownership comes from
the directly named TypeNames, not from their nominal supertypes. An exact union
therefore meets the owners of its representation-stable arms; an unproved arm
set conservatively returns package-type top (wide open).
"""
function arg0_invariant_package_owner(@nospecialize(type))
    return _arg0_invariant_package_owner(type, TypeVar[])
end

function _arg0_package_owner(@nospecialize(type),
                             local_typevars::Vector{TypeVar})
    type === Bottom && return _arg0_package_bottom()
    if type isa Union
        owner = _arg0_package_bottom()
        for arm in uniontypes(type)
            owner = _arg0_package_join(
                owner, _arg0_package_owner(arm, local_typevars))
        end
        return owner
    elseif type isa UnionAll
        push!(local_typevars, type.var)
        owner = _arg0_package_owner(type.body, local_typevars)
        pop!(local_typevars)
        return owner
    elseif type isa TypeVar
        return _arg0_package_owner(type.ub, local_typevars)
    elseif isType(type)
        return _arg0_invariant_package_owner(
            type_parameter(type), local_typevars)
    elseif type isa DataType
        closed_in = type.name.dispatch_closed_in
        closed_in === nothing && return _arg0_package_top()
        return _arg0_package_atom(closed_in::Module)
    end
    return _arg0_package_top()
end

"""
    arg0_package_owner(T::Type)

Return the positive package formula whose roots close dispatch over a callable
first-argument region `T`. Ordinary callable types use their TypeName's
finalized `dispatch_closed_in` root. Unions join independently closed regions;
`Union{}` has no region; and an open TypeName contributes package-type top,
which makes the combined region wide open.

Exact type-object regions use [`arg0_invariant_package_owner`](@ref), reflecting
the ownership of constructor-like dispatch by the TypeNames named inside
`Type{...}`.
"""
function arg0_package_owner(@nospecialize(type::Type))
    return _arg0_package_owner(type, TypeVar[])
end

function _package_owner_portion_is_self_owned(portion, self_rights)
    self_rights === nothing && return false
    for right in self_rights.alternatives
        all(right.factors) do factor
            any(candidate -> candidate === factor, portion.factors)
        end && return true
    end
    return false
end

function _package_owner_is_closed_or_self(owner, self_rights,
                                          factor_is_closed)
    for portion in owner.alternatives
        _package_owner_portion_is_self_owned(portion, self_rights) && continue
        isempty(portion.factors) && return false
        all(factor_is_closed, portion.factors) || return false
    end
    return true
end

function _package_owner_factor_is_closed(factor::Module)
    factor === Base && return true
    for node in package_graph_nodes(REQUIRES_GRAPH)
        node.root_module === factor || continue
        return !package_graph_node_is_open(REQUIRES_GRAPH, node)
    end
    return false
end

function _arg0_package_owner_is_closed_or_self(@nospecialize(type::Type),
                                               self_rights)
    # At ordinary runtime, world-age backedges and invalidation protect the
    # current lookup. The package-owner gate only controls assumptions stored
    # in an incremental output image.
    generating_output(true) || return true
    owner = arg0_package_owner(type)
    return _package_owner_is_closed_or_self(
        owner, self_rights, _package_owner_factor_is_closed)
end

struct DefinitionPiracyViolation
    kind::Symbol
    conflicting_method::Union{Nothing,Method}
end

function _definition_arg0(@nospecialize(sig::Type))
    body = unwrap_unionall(sig)
    @assert body isa DataType && body.name === Tuple.name
    parameters = body.parameters
    @assert !isempty(parameters)
    index = parameters[1] === typeof(Core.kwcall) && length(parameters) >= 3 ? 3 : 1
    arg0 = parameters[index]
    while arg0 isa TypeVar
        arg0 = arg0.ub
    end
    return arg0::Type
end

function _has_externally_closed_arg0(@nospecialize(sig::Type), self_rights)
    owner = arg0_package_owner(_definition_arg0(sig))
    for portion in owner.alternatives
        # An empty conjunction represents an open dispatch region, not an
        # external package's closure authority.
        isempty(portion.factors) && continue
        _package_owner_portion_is_self_owned(portion, self_rights) || return true
    end
    return false
end

function _definition_covering_interfaces(candidate::Method, world::UInt)
    covering = Method[]
    lookup = raw_interface_matches(candidate.sig, world)
    lookup === nothing && return nothing
    for interface_match in lookup.matches
        interface = interface_match.match.method
        candidate.sig <: interface.sig || continue
        push!(covering, interface)
    end
    if get_methodtable(candidate) === Core.interfacetable
        # The candidate has not reached the interface table yet. It nevertheless
        # grants exactly the implementation permission it is declaring.
        push!(covering, candidate)
    end
    return covering
end

"""
    definition_piracy_violations(candidate, implementation_rights, world)

Check the type- and implementation-piracy policy for a Method immediately
before it is inserted. The returned violations do not change dispatch; the
runtime's `--piracy` policy decides whether to ignore, warn, or reject them.

An externally closed callable region requires the candidate to be contained in
an interface. If the candidate is more specific than an existing Method from a
different package root, one of its covering interfaces must also be more
specific than that Method. Methods in the candidate's own package root do not
consume its interface permission.
"""
function definition_piracy_violations(candidate::Method,
                                      implementation_rights, world::UInt)
    result = Base.packagetype(candidate.sig)
    if !Base._packagetype_leq(
            Base._packagetype_upper(result), implementation_rights)
        kind = Base.ispackagetypeexact(result) ?
            :type_piracy : :unproven_type_ownership
        return DefinitionPiracyViolation[
            DefinitionPiracyViolation(kind, nothing)
        ]
    end

    _has_externally_closed_arg0(candidate.sig, implementation_rights) ||
        return DefinitionPiracyViolation[]

    covering = _definition_covering_interfaces(candidate, world)
    covering === nothing && return nothing
    isempty(covering) && return DefinitionPiracyViolation[
        DefinitionPiracyViolation(:missing_interface, nothing)
    ]

    methods = raw_method_matches(candidate.sig, world)
    methods === nothing && return nothing
    candidate_root = moduleroot(candidate.module)
    violations = DefinitionPiracyViolation[]
    for method_match in methods.matches
        method = method_match.method
        moduleroot(method.module) === candidate_root && continue
        morespecific(candidate.sig, method.sig) || continue
        any(interface -> morespecific(interface.sig, method.sig), covering) &&
            continue
        push!(violations,
              DefinitionPiracyViolation(:uncovered_specialization, method))
    end

    # TODO: Restrict cross-package specificity using the requires graph before
    # relying on this policy to avoid invalidation. For now this intentionally
    # uses the ordinary `≺:` relation exactly as dispatch does.
    return violations
end
