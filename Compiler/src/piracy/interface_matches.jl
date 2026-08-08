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

"""
    interface_matches(methods, interfaces) -> Vector{InterfaceMatch}

Compute a conservative set of open interface regions for one implementation
authority. `methods` must contain every raw applicable Method owned outside the
authority, and `interfaces` must contain every raw applicable interface usable
by that authority, in the narrow-to-broad order produced by
`raw_interface_matches`. Neither input may have been filtered by ordinary
dispatch.

The result guarantees that every call point open to a future implementation is
contained in the union of the returned interfaces' query-local `spec_types`.
"""
function interface_matches(methods::Vector{MethodMatch},
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
                return interfaces[open_interfaces]
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
                return interfaces[open_interfaces]
        end

        all(resolved_interfaces) && return interfaces[open_interfaces]
        progress && continue

        # The unresolved component has no inductive first step. Choose the
        # narrowest remaining interface as the coinductive open seed.
        seed = findfirst(!, resolved_interfaces)::Int
        R = mark_open!(seed, interfaces[seed].match.spec_types, R)
        interfaces[seed].match.fully_covers && return interfaces[open_interfaces]
    end
end

function filter_open_callees(callees::Vector{MethodMatch},
                             open_interfaces::Vector{InterfaceMatch})
    open_regions = Any[match.match.spec_types for match in open_interfaces]
    open_union = isempty(open_regions) ? Union{} : Union{open_regions...}
    return filter(callees) do callee
        !(callee.spec_types <: open_union)
    end
end
