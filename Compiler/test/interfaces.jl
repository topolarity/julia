# This file is a part of Julia. License is MIT: https://julialang.org/license

module interfaces

using Test

include("setup_Compiler.jl")

module InterfaceMatchFixtures
interface_more_specific(x) = x
interface interface_more_specific(::Int)::Int

interface method_more_specific(::Any)
method_more_specific(::Int) = nothing

equal_specificity(::Int) = nothing
interface equal_specificity(::Int)

interface parametric_interface(::T)::Ref{T} where {T}

undefined_param_interface(::Union{T,Nothing}, ::Union{T,Nothing}) where {T} = nothing
interface undefined_param_interface(::Union{T,Nothing}, ::Union{T,Nothing})::Ref{T} where {T}

disjoint_interface(::Int) = nothing
interface disjoint_interface(::String)

union_covered(::Int) = nothing
union_covered(::String) = nothing
interface union_covered(::Union{Int,String})

raw_complete(::T, ::Vararg{T}) where {T<:Integer} = :diagonal
raw_complete(::Integer, ::Vararg{Union{Int,String}}) = :union
raw_complete(::Integer, ::Vararg{String}) = :string

coinductive_cycle(::T, ::Vararg{T}) where {T<:Integer} = :diagonal
coinductive_cycle(::Integer, ::Vararg{Union{Int,String}}) = :union
interface coinductive_cycle(::Integer, ::Integer)
interface coinductive_cycle(::Integer, ::Vararg{String})

interface broad_seed(::Any)
interface broad_seed(::Int)

contract_minimized(x::Bool) = x ? 1 : "bad"
interface contract_minimized(::Any)::Any
interface contract_minimized(::Integer)::Number
interface contract_minimized(::Bool)::Int

function ownership_only end
end

arg0_package_p = Core.eval(Base.__toplevel__, :(module Arg0PackageP
    abstract type AbstractCallable end
    struct CallableA <: AbstractCallable end
    struct CallableB <: AbstractCallable end
end))

arg0_package_q = Core.eval(Base.__toplevel__, :(module Arg0PackageQ end))
Core.eval(arg0_package_q,
    :(struct CallableC <: $arg0_package_p.AbstractCallable end))

function has_package_type_portion(package_type, factors...)
    return any(package_type.alternatives) do portion
        length(portion.factors) == length(factors) &&
            all(factor -> any(candidate -> candidate === factor, portion.factors), factors)
    end
end

is_package_type_bottom(package_type) = isempty(package_type.alternatives)

@testset "arg0 package owner" begin
    open_owner = Compiler.arg0_package_owner(Any)
    @test has_package_type_portion(open_owner)

    # Function forwards dispatch ownership to its subtypes.
    function_owner = Compiler.arg0_package_owner(Function)
    @test has_package_type_portion(function_owner)

    @test is_package_type_bottom(Compiler.arg0_package_owner(Union{}))

    p_owner = Compiler.arg0_package_owner(arg0_package_p.CallableA)
    @test has_package_type_portion(p_owner, arg0_package_p)

    union_owner = Compiler.arg0_package_owner(Union{
        arg0_package_p.CallableA,
        arg0_package_q.CallableC,
    })
    @test has_package_type_portion(union_owner, arg0_package_p)
    # Callable subtypes inherit dispatch closure from their supertype.
    @test !has_package_type_portion(union_owner, arg0_package_q)

    type_owner = Compiler.arg0_package_owner(Type{arg0_package_p.CallableA})
    @test has_package_type_portion(type_owner, arg0_package_p)

    # Exact constructor ownership does not charge nominal supertypes.
    subtype_type_owner = Compiler.arg0_package_owner(Type{arg0_package_q.CallableC})
    @test has_package_type_portion(subtype_type_owner, arg0_package_q)
    @test !has_package_type_portion(
        subtype_type_owner, arg0_package_p, arg0_package_q)

    union_type_owner = Compiler.arg0_package_owner(Type{Union{
        arg0_package_p.CallableA,
        arg0_package_q.CallableC,
    }})
    @test has_package_type_portion(
        union_type_owner, arg0_package_p, arg0_package_q)

    same_package_union = Compiler.arg0_package_owner(Type{Union{
        arg0_package_p.CallableA,
        arg0_package_p.CallableB,
    }})
    @test has_package_type_portion(same_package_union, arg0_package_p)

    # A constructor family does not give the abstract TypeName's package
    # ownership of constructor dispatch for arbitrary future subtypes.
    abstract_family = Type{T} where T<:arg0_package_p.AbstractCallable
    @test has_package_type_portion(
        Compiler.arg0_package_owner(abstract_family))

    @test has_package_type_portion(
        Compiler.arg0_package_owner(Type{Union{}}), Base)

    p_formula = Base._packagetype_atom(arg0_package_p)
    q_formula = Base._packagetype_atom(arg0_package_q)
    joined_formula = Base._packagetype_join(p_formula, q_formula)
    met_formula = Base._packagetype_meet(p_formula, q_formula)
    factor_p_is_closed = factor -> factor === arg0_package_p
    no_factor_is_closed = factor -> false
    @test Compiler._package_owner_is_closed_or_self(
        Base._packagetype_bottom(), nothing, no_factor_is_closed)
    @test !Compiler._package_owner_is_closed_or_self(
        Base._packagetype_top(), nothing, no_factor_is_closed)
    @test Compiler._package_owner_is_closed_or_self(
        p_formula, nothing, factor_p_is_closed)
    @test Compiler._package_owner_is_closed_or_self(
        p_formula, p_formula, no_factor_is_closed)
    @test Compiler._package_owner_is_closed_or_self(
        joined_formula, q_formula, factor_p_is_closed)
    @test !Compiler._package_owner_is_closed_or_self(
        joined_formula, nothing, factor_p_is_closed)
    @test Compiler._package_owner_is_closed_or_self(
        met_formula, p_formula, no_factor_is_closed)
    @test Compiler._arg0_package_owner_is_closed_or_self(Any, nothing)
end

@testset "call extensibility" begin
    raw_methods(@nospecialize(sig)) = begin
        result = Compiler.raw_method_matches(sig, Base.get_world_counter())
        Core.MethodMatch[match for match in result.matches]
    end
    raw_interfaces(@nospecialize(sig)) = begin
        result = Compiler.raw_interface_matches(sig, Base.get_world_counter())
        Core.InterfaceMatch[match for match in result.matches]
    end

    ims_sig = Tuple{typeof(InterfaceMatchFixtures.interface_more_specific),Int}
    ims_methods = raw_methods(ims_sig)
    ims_interfaces = raw_interfaces(ims_sig)
    @test only(ims_interfaces).rettype === Int
    @test Compiler._in_interface_interferences(
        only(ims_interfaces).match.method, only(ims_methods).method)
    @test !Compiler._in_interface_interferences(
        only(ims_methods).method, only(ims_interfaces).match.method)
    ims_callees, ims_future = Compiler.resolve_call_extensibility(
        ims_methods, ims_interfaces)
    @test only(ims_future).spec_types === only(ims_interfaces).match.spec_types
    @test isempty(ims_callees)

    mms_sig = Tuple{typeof(InterfaceMatchFixtures.method_more_specific),Int}
    mms_methods = raw_methods(mms_sig)
    mms_interfaces = raw_interfaces(mms_sig)
    @test Compiler._in_interface_interferences(
        only(mms_methods).method, only(mms_interfaces).match.method)
    @test !Compiler._in_interface_interferences(
        only(mms_interfaces).match.method, only(mms_methods).method)
    mms_callees, mms_future = Compiler.resolve_call_extensibility(
        mms_methods, mms_interfaces)
    @test mms_callees == mms_methods
    @test isempty(mms_future)

    equal_sig = Tuple{typeof(InterfaceMatchFixtures.equal_specificity),Int}
    equal_methods = raw_methods(equal_sig)
    equal_interfaces = raw_interfaces(equal_sig)
    @test Compiler._in_interface_interferences(
        only(equal_interfaces).match.method, only(equal_methods).method)
    @test Compiler._in_interface_interferences(
        only(equal_methods).method, only(equal_interfaces).match.method)
    equal_callees, equal_future = Compiler.resolve_call_extensibility(
        equal_methods, equal_interfaces)
    @test equal_callees == equal_methods
    @test isempty(equal_future)

    parametric_sig = Tuple{typeof(InterfaceMatchFixtures.parametric_interface),Int}
    parametric_interfaces = raw_interfaces(parametric_sig)
    @test only(parametric_interfaces).rettype === Ref{Int}
    parametric_callees, parametric_future = Compiler.resolve_call_extensibility(
        Core.MethodMatch[], parametric_interfaces)
    @test isempty(parametric_callees)
    @test only(parametric_future).spec_types ===
        only(parametric_interfaces).match.spec_types

    undefined_param_sig = Tuple{
        typeof(InterfaceMatchFixtures.undefined_param_interface),Nothing,Nothing}
    undefined_param_interfaces = raw_interfaces(undefined_param_sig)
    @test only(undefined_param_interfaces).rettype === nothing
    @test Compiler.future_return_type(
        Compiler.AnyFutureMethodMatch(undefined_param_sig),
        undefined_param_interfaces) === Any

    disjoint_sig = Tuple{typeof(InterfaceMatchFixtures.disjoint_interface),Union{Int,String}}
    disjoint_methods = raw_methods(disjoint_sig)
    disjoint_interfaces = raw_interfaces(disjoint_sig)
    @test Compiler._interface_pair_relation(
        only(disjoint_interfaces), only(disjoint_methods)) == (false, false)
    disjoint_callees, disjoint_future = Compiler.resolve_call_extensibility(
        disjoint_methods, disjoint_interfaces)
    @test disjoint_callees == disjoint_methods
    @test only(disjoint_future).spec_types ===
        only(disjoint_interfaces).match.spec_types

    union_sig = Tuple{typeof(InterfaceMatchFixtures.union_covered),Union{Int,String}}
    union_methods = raw_methods(union_sig)
    union_callees, union_future = Compiler.resolve_call_extensibility(
        union_methods, raw_interfaces(union_sig))
    @test union_callees == union_methods
    @test isempty(union_future)

    raw_complete_sig = Tuple{typeof(InterfaceMatchFixtures.raw_complete),Integer,Vararg{Any}}
    @test length(raw_methods(raw_complete_sig)) == 3

    cycle_sig = Tuple{typeof(InterfaceMatchFixtures.coinductive_cycle),Integer,Vararg{Any}}
    cycle_methods = raw_methods(cycle_sig)
    cycle_interfaces = raw_interfaces(cycle_sig)
    @test all(cycle_methods) do method
        any(interface_match ->
            last(Compiler._interface_pair_relation(interface_match, method)),
            cycle_interfaces)
    end
    @test all(cycle_interfaces) do interface_match
        any(cycle_methods) do method
            intersects, opens =
                Compiler._interface_pair_relation(interface_match, method)
            intersects && !opens
        end
    end
    cycle_callees, cycle_future = Compiler.resolve_call_extensibility(
        cycle_methods, cycle_interfaces)
    @test cycle_callees == cycle_methods
    @test length(cycle_future) == 2
    @test all(cycle_interfaces) do interface_match
        any(match -> match.spec_types === interface_match.match.spec_types,
            cycle_future)
    end

    seed_sig = Tuple{typeof(InterfaceMatchFixtures.broad_seed),Any}
    sorted_seeds = raw_interfaces(seed_sig)
    @test sorted_seeds[1].match.spec_types <: sorted_seeds[2].match.spec_types
    @test !(sorted_seeds[2].match.spec_types <: sorted_seeds[1].match.spec_types)
end

@testset "callee interface contracts" begin
    f = InterfaceMatchFixtures.contract_minimized
    sig = Tuple{typeof(f),Bool}
    lookup = Compiler.raw_interface_matches(sig, Base.get_world_counter())
    @test lookup !== nothing
    @test length(lookup.matches) == 3
    contracts = Compiler.minimize_interface_contracts(lookup.matches)
    @test length(contracts) == 1
    @test only(contracts).rettype === Int
end

@testset "semantic inference matches" begin
    world = Base.get_world_counter()
    table = Compiler.InternalMethodTable(world)

    f = InterfaceMatchFixtures.interface_more_specific
    sig = Tuple{typeof(f),Int}
    result = Compiler.inference_matches(sig, table, world)
    @test result isa Compiler.InferenceLookupResult
    @test isempty(result.matches)
    @test result.fullmatch
    @test result.unordered
    @test length(result.future) == 1
    @test only(result.future).spec_types === sig
    @test Compiler.future_return_type(
        only(result.future), result.interfaces) === Int

    raw_interfaces = Compiler.raw_interface_matches(sig, world)
    fully_open = Compiler._fully_open_inference_result(sig, raw_interfaces)
    @test isempty(fully_open.matches)
    @test only(fully_open.future).spec_types === sig
    @test fully_open.interfaces == raw_interfaces.matches
    @test !fully_open.fullmatch
    @test fully_open.unordered
    @test fully_open.valid_worlds == raw_interfaces.valid_worlds

    f = InterfaceMatchFixtures.method_more_specific
    sig = Tuple{typeof(f),Int}
    result = Compiler.inference_matches(sig, table, world)
    @test result isa Compiler.InferenceLookupResult
    @test length(result.matches) == 1
    @test isempty(result.future)
    @test result.fullmatch
    @test !result.unordered
    @test length(result.interfaces) == 1

    f = InterfaceMatchFixtures.parametric_interface
    sig = Tuple{typeof(f),Int}
    result = Compiler.inference_matches(sig, table, world)
    @test result isa Compiler.InferenceLookupResult
    @test isempty(result.matches)
    @test length(result.future) == 1
    @test Compiler.future_return_type(
        only(result.future), result.interfaces) === Ref{Int}
    @test !result.fullmatch
    @test result.unordered

    f = InterfaceMatchFixtures.ownership_only
    sig = Tuple{typeof(f),Int}
    result = Compiler.inference_matches(sig, table, world)
    @test result isa Compiler.InferenceLookupResult
    @test isempty(result.matches)
    @test isempty(result.interfaces)
    @test isempty(result.future)
    @test !result.fullmatch
    @test !result.unordered
    @test world in result.valid_worlds

    empty_callees, empty_future = Compiler.resolve_call_extensibility(
        Core.MethodMatch[], Core.InterfaceMatch[])
    @test isempty(empty_callees)
    @test isempty(empty_future)

    @test_throws ArgumentError Compiler.inference_matches(
        Tuple{typeof(f),Int}, table, world - 1)
end

definition_policy_p = Core.eval(Base.__toplevel__, :(module DefinitionPolicyP
    type_piracy_target(x) = x

    function missing_interface end

    function local_extension end
    interface local_extension(::Any, ::Any)

    specialization_blocked(::Any, ::Any) = nothing
    interface specialization_blocked(::Any, ::Any)

    specialization_allowed(::Any, ::Any) = nothing
    interface specialization_allowed(::Any, ::Any)
    interface specialization_allowed(::Int, ::Any)

    function interface_candidate end
end))

definition_policy_q = Core.eval(Base.__toplevel__, :(module DefinitionPolicyQ end))
Core.eval(definition_policy_q, :(const P = $definition_policy_p))
Core.eval(definition_policy_q, quote
    struct Bar end
    P.type_piracy_target(::Int) = nothing
    P.missing_interface(::Any, ::Bar) = nothing
    P.local_extension(::Any, ::Bar) = nothing
    P.local_extension(::Int, ::Bar) = nothing
    P.specialization_blocked(::Int, ::Bar) = nothing
    P.specialization_allowed(::Int, ::Bar) = nothing
    interface P.interface_candidate(::Bar)
end)

function definition_method(root::Module, @nospecialize(signature::Type))
    for method in methods(signature.parameters[1].instance)
        method.module === root || continue
        method.sig == signature && return method
    end
    error("definition Method not found for $signature")
end

function definition_interface(root::Module, @nospecialize(signature::Type))
    lookup = Compiler.raw_interface_matches(signature, Base.get_world_counter())
    for match in lookup.matches
        method = match.match.method
        method.module === root || continue
        method.sig == signature && return method
    end
    error("definition interface not found for $signature")
end

@testset "definition piracy policy" begin
    P = definition_policy_p
    Q = definition_policy_q
    Bar = Q.Bar
    rights = Base._packagetype_atom(Q)
    world = Base.get_world_counter()
    violation_kinds(method) = map(
        violation -> violation.kind,
        Compiler.definition_piracy_violations(method, rights, world))

    type_piracy = definition_method(
        Q, Tuple{typeof(P.type_piracy_target),Int})
    @test violation_kinds(type_piracy) == [:type_piracy]

    missing_interface = definition_method(
        Q, Tuple{typeof(P.missing_interface),Any,Bar})
    @test violation_kinds(missing_interface) == [:missing_interface]

    broad_local = definition_method(
        Q, Tuple{typeof(P.local_extension),Any,Bar})
    narrow_local = definition_method(
        Q, Tuple{typeof(P.local_extension),Int,Bar})
    @test isempty(violation_kinds(broad_local))
    # A Method from the same package root does not consume the permission
    # granted by the broad interface.
    @test isempty(violation_kinds(narrow_local))

    blocked = definition_method(
        Q, Tuple{typeof(P.specialization_blocked),Int,Bar})
    @test violation_kinds(blocked) == [:uncovered_specialization]

    allowed = definition_method(
        Q, Tuple{typeof(P.specialization_allowed),Int,Bar})
    @test isempty(violation_kinds(allowed))

    interface_candidate = definition_interface(
        Q, Tuple{typeof(P.interface_candidate),Bar})
    @test isempty(violation_kinds(interface_candidate))
end

@testset "definition piracy command-line policy" begin
    setup = """
        parent = Core.eval(Base.__toplevel__, :(module PiracyCLIParent
            target(x) = x
        end))
        child = Core.eval(Base.__toplevel__, :(module PiracyCLIChild end))
        Core.eval(child, :(const Parent = \$parent))
        ccall(:jl_set_module_uuid, Cvoid, (Any, NTuple{2, UInt64}),
            child, (UInt64(1), UInt64(2)))
        Base._set_root_module_implementation_rights!(
            child, Base._packagetype_atom(child))
        """
    definition = "Core.eval(child, :(Parent.target(::Int) = nothing))"

    function run_policy(policy, script)
        err = IOBuffer()
        cmd = `$(Base.julia_cmd()) --startup-file=no --piracy=$policy -e $script`
        process = run(pipeline(ignorestatus(cmd); stdout=devnull, stderr=err))
        return success(process), String(take!(err))
    end

    succeeded, warning = run_policy("warn", "$setup\n$definition")
    @test succeeded
    @test occursin("type piracy", warning)
    @test occursin("target(::Int64)", warning)
    @test !occursin("Tuple{typeof", warning)

    strict_script = """
        $setup
        rejected = false
        try
            $definition
        catch err
            global rejected = true
            showerror(stderr, err)
            println(stderr)
        end
        rejected || error("strict piracy policy accepted the definition")
        any(methods(parent.target)) do method
            method.module === child &&
                method.sig == Tuple{typeof(parent.target),Int}
        end && error("strict piracy policy published the rejected definition")
        """
    succeeded, strict_error = run_policy("strict", strict_script)
    @test succeeded
    @test occursin("type piracy", strict_error)

    succeeded, silence = run_policy("off", "$setup\n$definition")
    @test succeeded
    @test !occursin("piracy", silence)
end

end # module interfaces
