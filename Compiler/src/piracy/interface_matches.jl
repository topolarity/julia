# This file is a part of Julia. License is MIT: https://julialang.org/license

# Whether `peer` occurs in the holder-relative cross-table interference set.
# For an intersecting pair, membership means `holder ≺/: peer`.
function _in_interface_interferences(peer::Method, holder::Method)
    interferences = holder.interface_interferences
    for i = 1:length(interferences)
        isassigned(interferences, i) || break
        interferences[i] === peer && return true
    end
    return false
end

function _interface_pair_relation(interface_match::InterfaceMatch, method::MethodMatch)
    interface_method = interface_match.match.method
    ordinary_method = method.method
    interface_in_method =
        _in_interface_interferences(interface_method, ordinary_method)
    method_in_interface =
        _in_interface_interferences(ordinary_method, interface_method)
    intersects = interface_in_method | method_in_interface
    interface_opens = interface_in_method & !method_in_interface
    return intersects, interface_opens
end

function _interface_future_matches(methods::Vector{MethodMatch},
                                   interfaces::Vector{InterfaceMatch})
    nmethods = length(methods)
    ninterfaces = length(interfaces)
    openers = [Int[] for _ = 1:nmethods]
    blockers = [Int[] for _ = 1:ninterfaces]
    for interface_index = 1:ninterfaces
        interface_match = interfaces[interface_index]
        for method_index = 1:nmethods
            intersects, interface_opens =
                _interface_pair_relation(interface_match, methods[method_index])
            intersects || continue
            if interface_opens
                push!(openers[method_index], interface_index)
            else
                push!(blockers[interface_index], method_index)
            end
        end
    end

    resolved_methods = falses(nmethods)
    resolved_interfaces = falses(ninterfaces)
    open_interfaces = falses(ninterfaces)
    R = Union{}

    function result()
        future = AnyFutureMethodMatch[]
        for interface_index = 1:ninterfaces
            open_interfaces[interface_index] || continue
            _push_future_match!(
                future, interfaces[interface_index].match.spec_types)
        end
        return future
    end

    function mark_resolved!(resolved::BitVector, index::Int)
        resolved[index] = true
        return nothing
    end

    function mark_closed!(method_index::Int, @nospecialize(region),
                          @nospecialize(R))
        mark_resolved!(resolved_methods, method_index)
        return Union{R, region}
    end

    function mark_open!(interface_index::Int, @nospecialize(region),
                        @nospecialize(R))
        mark_resolved!(resolved_interfaces, interface_index)
        open_interfaces[interface_index] = true
        return Union{R, region}
    end

    while true
        progress = false
        for method_index = 1:nmethods
            resolved_methods[method_index] && continue
            method = methods[method_index]
            region = method.spec_types
            if region <: R
                mark_resolved!(resolved_methods, method_index)
                progress = true
            elseif all(interface_index -> resolved_interfaces[interface_index],
                       openers[method_index])
                R = mark_closed!(method_index, region, R)
                progress = true
            end
            resolved_methods[method_index] && method.fully_covers &&
                return result()
        end

        for interface_index = 1:ninterfaces
            resolved_interfaces[interface_index] && continue
            interface_match = interfaces[interface_index]
            region = interface_match.match.spec_types
            if region <: R
                mark_resolved!(resolved_interfaces, interface_index)
                progress = true
            elseif all(method_index -> resolved_methods[method_index],
                       blockers[interface_index])
                R = mark_open!(interface_index, region, R)
                progress = true
            end
            resolved_interfaces[interface_index] && interface_match.match.fully_covers &&
                return result()
        end

        all(resolved_interfaces) && return result()
        progress && continue

        # The unresolved component has no inductive first step. Choose the
        # narrowest remaining interface as the coinductive open seed.
        seed = findfirst(!, resolved_interfaces)::Int
        R = mark_open!(seed, interfaces[seed].match.spec_types, R)
        interfaces[seed].match.fully_covers && return result()
    end
end

function _region_union(regions)
    region_union = Bottom
    for region in regions
        region_union = Union{region_union, region}
    end
    return region_union
end

function _productive_future_region(@nospecialize(region))
    result = Base.packagetype(region)
    return !isempty(Base._packagetype_lower(result).alternatives)
end

function _push_future_match!(future::Vector{AnyFutureMethodMatch},
                             @nospecialize(region))
    _productive_future_region(region) || return false
    any(match -> match.spec_types == region, future) && return false
    push!(future, AnyFutureMethodMatch(region))
    return true
end

function filter_future_callees(callees::Vector{MethodMatch},
                               future::Vector{AnyFutureMethodMatch})
    open_union = _region_union(match.spec_types for match in future)
    return filter(callees) do callee
        !(callee.spec_types <: open_union)
    end
end

"""
    resolve_call_extensibility(callees, methods, interfaces)
        -> (callees, future)

Resolve conservative future-Method bounds and remove current callees whose
complete query-local regions are covered by them. `methods` must contain every
raw applicable Method, while `callees` is the already dispatch-resolved and
ordered Method list. `interfaces` must contain every raw applicable interface
in the narrow-to-broad order produced by `raw_interface_matches`.

The two-argument form uses the raw Method list as the callee list as well.
Neither `methods` nor `interfaces` may have undergone ordinary dispatch
filtering.
"""
function resolve_call_extensibility(callees::Vector{MethodMatch},
                                    methods::Vector{MethodMatch},
                                    interfaces::Vector{InterfaceMatch})
    future = _interface_future_matches(methods, interfaces)
    return filter_future_callees(callees, future), future
end

function resolve_call_extensibility(methods::Vector{MethodMatch},
                                    interfaces::Vector{InterfaceMatch})
    return resolve_call_extensibility(methods, methods, interfaces)
end

"""
    interface_contract(region, interfaces)

Return the cumulative successful-return bound from interfaces which each cover
all of `region`. The Boolean reports whether such a bound exists. Interfaces
which only overlap the region remain relevant to possible `ReturnTypeError`s,
but cannot narrow every successful return without splitting the region.
"""
function interface_contract(@nospecialize(region),
                            interfaces::Vector{InterfaceMatch})
    bound = Any
    constrained = false
    for interface_match in interfaces
        region <: interface_match.match.spec_types || continue
        rettype = interface_match.rettype
        # `nothing` records a contract template whose required static
        # parameter is undefined in this match. Dynamic dispatch raises a
        # contextual UndefVarError; until exception-aware contract inference
        # models that path, it contributes no successful-return refinement.
        rettype isa Type || continue
        bound = typeintersect(bound, rettype)
        constrained = true
    end
    return bound, constrained
end

function future_return_type(match::AnyFutureMethodMatch,
                            interfaces::Vector{InterfaceMatch})
    bound, constrained = interface_contract(match.spec_types, interfaces)
    return constrained ? bound : Any
end
