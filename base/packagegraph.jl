# This file is a part of Julia. License is MIT: https://julialang.org/license

"""
    LoadedPackageNode(module::Module)

Identify one loaded package instance by its root module. Two nodes compare equal
only when they contain the same root-module object; equal [`PkgId`](@ref)s do
not make separately loaded instances equal.
"""
struct LoadedPackageNode
    root_module::Module

    function LoadedPackageNode(mod::Module)
        return new(moduleroot(mod))
    end
end

function _root_module_new_typenames(root::Module)
    return ccall(:jl_root_module_new_typenames, Any, (Any,), root)
end

struct ModuleFinalizationState
    root_module::Module
    world::UInt
    new_typenames::IdSet{Core.TypeName}
    method_closed_typenames::IdSet{Core.TypeName}
    visited_typenames::IdSet{Core.TypeName}

    function ModuleFinalizationState(root::Module)
        root = moduleroot(root)
        inventory = _root_module_new_typenames(root)
        new_typenames = IdSet{Core.TypeName}()
        if inventory !== nothing
            for tn in inventory::Vector{Any}
                push!(new_typenames, tn::Core.TypeName)
            end
        end
        return new(root, get_world_counter(), new_typenames,
            IdSet{Core.TypeName}(), IdSet{Core.TypeName}())
    end
end

function _method_defined_using_typename(method::Method, tn::Core.TypeName)
    signature = unwrap_unionall(method.sig)
    parameters = signature.parameters
    isempty(parameters) && return false
    argument_index = 1
    if argument_datatypename(parameters[1]) === Core.Typeof(Core.kwcall).name
        length(parameters) >= 3 || return false
        argument_index = 3
    end
    argument = parameters[argument_index]
    for arm in uniontypes(argument)
        arm <: Type && continue
        argument_datatypename(arm) === tn && return true
    end
    return false
end

function _method_defined_using_typename(state::ModuleFinalizationState, tn::Core.TypeName)
    signature = Tuple{tn.wrapper, Vararg{Any}}
    min_world = RefValue{UInt}(typemin(UInt))
    max_world = RefValue{UInt}(typemax(UInt))
    has_ambig = RefValue{Int32}(0)
    matches = _methods_by_ftype(signature, nothing, -1, state.world, true,
        min_world, max_world, has_ambig)
    matches === nothing && return false
    for match in matches
        method = (match::Core.MethodMatch).method
        moduleroot(method.module) === state.root_module || continue
        _method_defined_using_typename(method, tn) && return true
    end
    return false
end

function _finalize_dispatch_closed_in!(state::ModuleFinalizationState, tn::Core.TypeName)
    tn in state.visited_typenames && return nothing
    wrapper = tn.wrapper
    inherited = nothing
    if wrapper !== Any
        super = supertype(wrapper)
        super_typename = typename(unwrap_unionall(super))
        if super_typename in state.new_typenames
            _finalize_dispatch_closed_in!(state, super_typename)
        end
        inherited = super_typename.dispatch_closed_in
    end
    dispatch_closed_in = if inherited !== nothing
        inherited
    elseif !isabstracttype(wrapper) || tn in state.method_closed_typenames
        state.root_module
    else
        nothing
    end
    Core.setfield!(tn, :dispatch_closed_in, dispatch_closed_in)
    push!(state.visited_typenames, tn)
    return nothing
end

"""
    _finalize_root_module(root::Module)

Finalize the root-module state accumulated while loading one package instance.
This is a package lifecycle event, not an image-serialization event: an image
may contain several independently finalized package instances. Completion also
records the root's monotonic `finalized` state in the runtime.
"""
function _finalize_root_module(root::Module)
    state = ModuleFinalizationState(root)
    for tn in state.new_typenames
        if _method_defined_using_typename(state, tn)
            push!(state.method_closed_typenames, tn)
        end
    end
    for tn in state.new_typenames
        _finalize_dispatch_closed_in!(state, tn)
    end
    ccall(:jl_root_module_finalize, Cvoid, (Any,), state.root_module)
    return nothing
end

==(a::LoadedPackageNode, b::LoadedPackageNode) = a.root_module === b.root_module
isequal(a::LoadedPackageNode, b::LoadedPackageNode) = a.root_module === b.root_module
hash(node::LoadedPackageNode, h::UInt) = hash(objectid(node.root_module), h)
PkgId(node::LoadedPackageNode) = PkgId(node.root_module)

function show(io::IO, node::LoadedPackageNode)
    print(io, "LoadedPackageNode(")
    show(io, node.root_module)
    print(io, ')')
end

function _package_require_targets(root::Module)
    requires = ccall(:jl_module_package_requires, Any, (Any,), root)
    requires === nothing && return nothing
    return requires::Vector{Any}
end

function _is_managed_package_root(root::Module)
    root === Core && return false
    root === Base && return false
    root === Main && return false
    return PkgId(root).uuid !== nothing
end

function _module_is_open(root::Module)
    # The runtime canonicalizes this argument to the same registered root used
    # by `moduleroot`, so callers cannot observe different openness for a
    # package and one of its submodules.
    return ccall(:jl_module_is_open, Cint, (Any,), root) != 0
end

function _has_package_require(root::Module, target::Module)
    requires = _package_require_targets(root)
    requires === nothing && return false
    return any(mod -> mod === target, requires)
end

function _has_package_require(root::Module, target::PkgId)
    requires = _package_require_targets(root)
    requires === nothing && return false
    return any(mod -> PkgId(mod::Module) == target, requires)
end

function _is_axiomatic_package_require(root::Module, target::Module)
    root === target && return true
    target === Core && return true
    target === Base && return true
    target === Compiler && return true
    return !_is_managed_package_root(root)
end

function _package_require_error(root::Module, target::PkgId)
    source = PkgId(root)
    return ErrorException("package $(source.name) cannot require $(target.name): " *
        "the module is closed to new requires edges")
end

function _check_package_require(root::Module, target::PkgId)
    @lock require_lock begin
        root = moduleroot(root)
        source = PkgId(root)
        source == target && return nothing
        !_is_managed_package_root(root) && return nothing
        _has_package_require(root, target) && return nothing
        _module_is_open(root) || throw(_package_require_error(root, target))
        return nothing
    end
end

function _check_package_require(into::Module, target::Module)
    @lock require_lock begin
        root = moduleroot(into)
        target = moduleroot(target)
        _is_axiomatic_package_require(root, target) && return nothing
        targetid = PkgId(target)
        _has_package_require(root, target) && return nothing
        _module_is_open(root) || throw(_package_require_error(root, targetid))
        return nothing
    end
end

function _record_package_require!(into::Module, target::Module)
    root = moduleroot(into)
    target = moduleroot(target)
    _is_axiomatic_package_require(root, target) && return nothing
    @lock require_lock begin
        ccall(:jl_module_add_package_require, Cvoid, (Any, Any), root, target)
    end
    return nothing
end

"""
    direct_package_requires(node::LoadedPackageNode)

Return the direct `≤R` successors of `node`: the loaded package instances which
`node` directly requires. The returned nodes retain instance identity, including
when multiple instances have the same [`PkgId`](@ref).
"""
function direct_package_requires(node::LoadedPackageNode)
    @lock require_lock begin
        requires = _package_require_targets(node.root_module)
        requires === nothing && return LoadedPackageNode[]
        required = LoadedPackageNode[]
        sizehint!(required, length(requires))
        for target in requires
            push!(required, LoadedPackageNode(target::Module))
        end
        return required
    end
end

"""
    requires_graph_node_is_open(node::LoadedPackageNode)

Return whether a managed package instance may acquire novel outgoing `≤R`
edges. This is exactly the existing openness of its module, shared by every
submodule belonging to the same loaded package instance.
"""
function requires_graph_node_is_open(node::LoadedPackageNode)
    root = node.root_module
    return _is_managed_package_root(root) && _module_is_open(root)
end

function loaded_package_nodes()
    modules = loaded_modules_array()
    nodes = LoadedPackageNode[]
    seen = IdSet{Module}()
    for mod in modules
        root = moduleroot(mod)
        _is_managed_package_root(root) || continue
        root in seen && continue
        push!(seen, root)
        push!(nodes, LoadedPackageNode(root))
    end
    return nodes
end
