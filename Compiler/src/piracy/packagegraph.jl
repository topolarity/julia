# This file is a part of Julia. License is MIT: https://julialang.org/license

abstract type AbstractPackageGraph end

"""
    DeclaredPackageGraph{N}(adjacency)

An identity-level package graph whose direct edges bound the package
requirements permitted by an environment. Nodes are normally `Base.PkgId`s.
The constructor copies and deduplicates the supplied adjacency. `IdDict` is
available during compiler bootstrap, and `Base.PkgId` has value `===` semantics.
"""
struct DeclaredPackageGraph{N} <: AbstractPackageGraph
    adjacency::IdDict{N,Vector{N}}

    DeclaredPackageGraph{N}(adjacency::IdDict{N,Vector{N}}, ::Nothing) where N =
        new{N}(adjacency)
end

function DeclaredPackageGraph{N}(adjacency) where N
    copied = IdDict{N,Vector{N}}()
    for (source, targets) in adjacency
        source = source::N
        successors = get!(Vector{N}, copied, source)
        for target in targets
            target = target::N
            target === source && continue
            any(successor -> successor === target, successors) || push!(successors, target)
            get!(Vector{N}, copied, target)
        end
    end
    return DeclaredPackageGraph{N}(copied, nothing)
end

DeclaredPackageGraph{N}() where N = DeclaredPackageGraph{N}(IdDict{N,Vector{N}}())

"""
    RequiresGraph()

The process-wide, instance-level graph of realized package requirements. Its
nodes are `Base.LoadedPackageNode`s and its edges are stored on the corresponding
root modules, so the view includes source-loaded and restored package instances.
"""
struct RequiresGraph <: AbstractPackageGraph end

const REQUIRES_GRAPH = RequiresGraph()

package_graph_nodes(graph::DeclaredPackageGraph) = collect(keys(graph.adjacency))
package_graph_nodes(::RequiresGraph) = Base.loaded_package_nodes()

function package_graph_direct_successors(graph::DeclaredPackageGraph{N}, node::N) where N
    return copy(get(graph.adjacency, node, N[]))
end

package_graph_direct_successors(::RequiresGraph, node) = Base.direct_package_requires(node)

package_graph_node_is_open(::DeclaredPackageGraph, node) = false
package_graph_node_is_open(::RequiresGraph, node) = Base.requires_graph_node_is_open(node)

function package_graph_has_direct_edge(graph::AbstractPackageGraph, source, target)
    return any(successor -> successor === target,
        package_graph_direct_successors(graph, source))
end

"""
    package_graph_reachable(graph, source, target)

Return whether `source <= target` in the reflexive, transitive closure of
`graph`. For `RequiresGraph`, this is the `≤R` relation.
"""
function package_graph_reachable(graph::AbstractPackageGraph, source::N, target::N) where N
    source === target && return true
    seen = IdSet{N}()
    push!(seen, source)
    pending = N[source]
    while !isempty(pending)
        current = pop!(pending)
        for successor in package_graph_direct_successors(graph, current)
            successor === target && return true
            successor in seen && continue
            push!(seen, successor)
            push!(pending, successor)
        end
    end
    return false
end
