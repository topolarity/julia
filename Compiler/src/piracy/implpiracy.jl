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
