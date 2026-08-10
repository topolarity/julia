# This file is a part of Julia. License is MIT: https://julialang.org/license

struct MethodLookupResult
    # Really Vector{Core.MethodMatch}, but it's easier to represent this as,
    # and work with, Vector{Any} on the C side.
    matches::Vector{Any}
    valid_worlds::WorldRange
    ambig::Bool
end

struct RawMethodLookupResult
    matches::Vector{MethodMatch}
    valid_worlds::WorldRange
end

struct RawInterfaceLookupResult
    # InterfaceMatch.rettype is a Type when its static-parameter template can
    # be instantiated, or `nothing` when a required parameter is undefined.
    matches::Vector{InterfaceMatch}
    valid_worlds::WorldRange
end

"""
    AnyFutureMethodMatch(spec_types)

Represent a query-local region in which inference must account for a future
selected Method without pretending that the Method already exists.
"""
struct AnyFutureMethodMatch
    spec_types::Type
end

"""
    InferenceLookupResult

The complete semantic lookup consumed by inference. `matches` contains only
real current callees. `future` contains possible future dispatch-table targets,
while `interfaces` retains every cumulative piecewise return contract.
`fullmatch` records current Method coverage before future-callee filtering.
`unordered` disables transformations which rely on the ordering of `matches`.
"""
struct InferenceLookupResult
    # Really Vector{Core.MethodMatch}, matching MethodLookupResult's C-friendly
    # representation and leaving future targets in their separate collection.
    matches::Vector{Any}
    future::Vector{AnyFutureMethodMatch}
    interfaces::Vector{InterfaceMatch}
    valid_worlds::WorldRange
    fullmatch::Bool
    unordered::Bool
end

function raw_method_matches(@nospecialize(sig::Type), world::UInt;
                            mt::Union{Nothing,MethodTable}=nothing)
    min_valid = RefValue{UInt}(typemin(UInt))
    max_valid = RefValue{UInt}(typemax(UInt))
    matches = _methods_by_ftype_raw(sig, mt, world, min_valid, max_valid)
    matches === nothing && return nothing
    typed_matches = MethodMatch[match::MethodMatch for match in matches]
    return RawMethodLookupResult(typed_matches, WorldRange(min_valid[], max_valid[]))
end

function raw_interface_matches(@nospecialize(sig::Type), world::UInt)
    min_valid = RefValue{UInt}(typemin(UInt))
    max_valid = RefValue{UInt}(typemax(UInt))
    matches = _interfaces_by_ftype_raw(sig, world, min_valid, max_valid)
    matches === nothing && return nothing
    typed_matches = InterfaceMatch[match::InterfaceMatch for match in matches]
    return RawInterfaceLookupResult(typed_matches, WorldRange(min_valid[], max_valid[]))
end

length(result::InferenceLookupResult) = length(result.matches)
function iterate(result::InferenceLookupResult, args...)
    r = iterate(result.matches, args...)
    r === nothing && return nothing
    match, state = r
    return (match::MethodMatch, state)
end
getindex(result::InferenceLookupResult, idx::Int) =
    getindex(result.matches, idx)::MethodMatch

length(result::MethodLookupResult) = length(result.matches)
function iterate(result::MethodLookupResult, args...)
    r = iterate(result.matches, args...)
    r === nothing && return nothing
    match, state = r
    return (match::MethodMatch, state)
end
getindex(result::MethodLookupResult, idx::Int) = getindex(result.matches, idx)::MethodMatch

abstract type MethodTableView end

"""
    struct InternalMethodTable <: MethodTableView

A struct representing the state of the internal method table at a
particular world age.
"""
struct InternalMethodTable <: MethodTableView
    world::UInt
end

"""
    struct OverlayMethodTable <: MethodTableView

Overlays the internal method table such that specific queries can be redirected to an
external table, e.g., to override existing methods.
"""
struct OverlayMethodTable <: MethodTableView
    world::UInt
    mt::MethodTable
end

struct MethodMatchKey
    sig # ::Type
    limit::Int
    MethodMatchKey(@nospecialize(sig), limit::Int) = new(sig, limit)
end

"""
    struct CachedMethodTable <: MethodTableView

Overlays another method table view with an additional local fast path cache that
can respond to repeated, identical queries faster than the original method table.
"""
struct CachedMethodTable{T<:MethodTableView} <: MethodTableView
    cache::IdDict{MethodMatchKey, Union{Nothing,MethodLookupResult}}
    table::T
end
CachedMethodTable(table::T) where T = CachedMethodTable{T}(IdDict{MethodMatchKey, Union{Nothing,MethodLookupResult}}(), table)

"""
    findall(sig::Type, view::MethodTableView; limit::Int=-1) ->
        matches::MethodLookupResult or nothing

Find all methods in the given method table `view` that are applicable to the given signature `sig`.
If no applicable methods are found, an empty result is returned.
If the number of applicable methods exceeded the specified `limit`, `nothing` is returned.
Note that the default setting `limit=-1` does not limit the number of applicable methods.
`overlayed` indicates if any of the matching methods comes from an overlayed method table.
"""
findall(@nospecialize(sig::Type), table::InternalMethodTable; limit::Int=-1) =
    _findall(sig, nothing, table.world, limit)

function findall(@nospecialize(sig::Type), table::OverlayMethodTable; limit::Int=-1)
    result = _findall(sig, table.mt, table.world, limit)
    result === nothing && return nothing
    nr = length(result)
    if nr ≥ 1 && result[nr].fully_covers
        # no need to fall back to the internal method table
        return result
    end
    # fall back to the internal method table
    fallback_result = _findall(sig, nothing, table.world, limit)
    fallback_result === nothing && return nothing
    # merge the fallback match results with the internal method table,
    # filtering out base methods that are fully covered by overlay methods
    overlay_matches = result.matches
    filtered = filter(fallback_result.matches) do base_match::MethodMatch
        dominated = any(overlay_matches) do overlay_match::MethodMatch
            base_match.method.sig <: overlay_match.method.sig
        end
        return !dominated
    end
    return MethodLookupResult(
        vcat(overlay_matches, filtered),
        WorldRange(
            max(result.valid_worlds.min_world, fallback_result.valid_worlds.min_world),
            min(result.valid_worlds.max_world, fallback_result.valid_worlds.max_world)),
        result.ambig | fallback_result.ambig)
end

function _findall(@nospecialize(sig::Type), mt::Union{Nothing,MethodTable}, world::UInt, limit::Int)
    _min_val = RefValue{UInt}(typemin(UInt))
    _max_val = RefValue{UInt}(typemax(UInt))
    _ambig = RefValue{Int32}(0)
    ms = _methods_by_ftype(sig, mt, limit, world, false, _min_val, _max_val, _ambig)
    isa(ms, Vector) || return nothing
    return MethodLookupResult(ms, WorldRange(_min_val[], _max_val[]), _ambig[] != 0)
end

function findall(@nospecialize(sig::Type), table::CachedMethodTable; limit::Int=-1)
    if isconcretetype(sig)
        # as for concrete types, we cache result at on the next level
        return findall(sig, table.table; limit)
    end
    key = MethodMatchKey(sig, limit)
    if haskey(table.cache, key)
        return table.cache[key]
    else
        return table.cache[key] = findall(sig, table.table; limit)
    end
end

_raw_method_matches(@nospecialize(sig::Type), table::InternalMethodTable) =
    raw_method_matches(sig, table.world)
_raw_method_matches(@nospecialize(sig::Type), table::CachedMethodTable) =
    _raw_method_matches(sig, table.table)

# A future overlay-specific query can combine its raw intersections with those
# of the internal table; until then the semantic lookup reports unsupported.
_raw_method_matches(@nospecialize(sig::Type), table::OverlayMethodTable) = nothing

_method_table_world(table::InternalMethodTable) = table.world
_method_table_world(table::OverlayMethodTable) = table.world
_method_table_world(table::CachedMethodTable) = _method_table_world(table.table)

function _call_signature_arg0(@nospecialize(sig::Type))
    body = unwrap_unionall(sig)
    @assert body isa DataType && body.name === Tuple.name
    @assert !isempty(body.parameters)
    arg0 = body.parameters[1]
    while arg0 isa TypeVar
        arg0 = arg0.ub
    end
    return arg0::Type
end

function _fully_open_inference_result(@nospecialize(sig::Type),
                                      interfaces::RawInterfaceLookupResult)
    return InferenceLookupResult(
        Any[], AnyFutureMethodMatch[AnyFutureMethodMatch(sig)],
        interfaces.matches, interfaces.valid_worlds, false, true)
end

"""
    inference_matches(sig, table, world, self_rights=nothing; limit=-1)

Combine ordinary Method dispatch resolution with complete raw Method/interface
intersections and first-argument package closure. During incremental output,
`self_rights` is the package-ownership formula granted to the current
definition transaction. Ordinary runtime bypasses the package-owner gate and
relies on world-age backedges and invalidation.
"""
function inference_matches(@nospecialize(sig::Type), table::MethodTableView,
                           world::UInt, self_rights=nothing; limit::Int=-1)
    world == _method_table_world(table) ||
        throw(ArgumentError("method-table and interface query worlds must agree"))

    interfaces = raw_interface_matches(sig, world)
    interfaces === nothing && return nothing

    arg0 = _call_signature_arg0(sig)
    if !_arg0_package_owner_is_closed_or_self(arg0, self_rights)
        return _fully_open_inference_result(sig, interfaces)
    end

    current = findall(sig, table; limit)
    current === nothing && return nothing

    methods = _raw_method_matches(sig, table)
    methods === nothing && return nothing

    matches = MethodMatch[match::MethodMatch for match in current.matches]
    matches, future = resolve_call_extensibility(
        matches, methods.matches, interfaces.matches)
    fullmatch = any(match::MethodMatch -> match.fully_covers, current)
    unordered = current.ambig | !isempty(future)
    valid_worlds = intersect(
        intersect(current.valid_worlds, methods.valid_worlds),
        interfaces.valid_worlds)
    return InferenceLookupResult(
        Any[matches...], future, interfaces.matches,
        valid_worlds, fullmatch, unordered)
end

"""
    findsup(sig::Type, view::MethodTableView) ->
        (match::Union{MethodMatch,Nothing}, valid_worlds::WorldRange, overlayed::Bool)

Find the (unique) method such that `sig <: match.method.sig`, while being more
specific than any other method with the same property. In other words, find the method
which is the least upper bound (supremum) under the specificity/subtype relation of
the queried `sig`nature. If `sig` is concrete, this is equivalent to asking for the method
that will be called given arguments whose types match the given signature.
Note that this query is also used to implement `invoke`.

Such a matching method `match` doesn't necessarily exist.
It is possible that no method is an upper bound of `sig`, or
it is possible that among the upper bounds, there is no least element.
In both cases `nothing` is returned.

`overlayed` indicates if any of the matching methods comes from an overlayed method table.
"""
findsup(@nospecialize(sig::Type), table::InternalMethodTable) =
    _findsup(sig, nothing, table.world)

function findsup(@nospecialize(sig::Type), table::OverlayMethodTable)
    match, valid_worlds = _findsup(sig, table.mt, table.world)
    match !== nothing && return match, valid_worlds
    # fall back to the internal method table
    fallback_match, fallback_valid_worlds = _findsup(sig, nothing, table.world)
    return (
        fallback_match,
        WorldRange(
            max(valid_worlds.min_world, fallback_valid_worlds.min_world),
            min(valid_worlds.max_world, fallback_valid_worlds.max_world)))
end

function _findsup(@nospecialize(sig::Type), mt::Union{Nothing,MethodTable}, world::UInt)
    min_valid = RefValue{UInt}(typemin(UInt))
    max_valid = RefValue{UInt}(typemax(UInt))
    match = ccall(:jl_gf_invoke_lookup_worlds, Any, (Any, Any, UInt, Ptr{Csize_t}, Ptr{Csize_t}),
                   sig, mt, world, min_valid, max_valid)::Union{MethodMatch, Nothing}
    valid_worlds = WorldRange(min_valid[], max_valid[])
    return match, valid_worlds
end

# This query is not cached
findsup(@nospecialize(sig::Type), table::CachedMethodTable) = findsup(sig, table.table)
