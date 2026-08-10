# This file is a part of Julia. License is MIT: https://julialang.org/license

# Package-type analysis must preserve exact type identity without inventing
# productive witnesses for degenerate types.

using Test

package_p = Core.eval(Base.__toplevel__, :(module PackagetypeTestP
    abstract type AbstractFoo end
    struct Foo <: AbstractFoo end

    abstract type HiddenSuper{T} end
    struct HiddenConcrete <: HiddenSuper{Tuple{}} end
    abstract type HiddenMiddle <: HiddenSuper{Tuple{}} end
    struct HiddenLeaf <: HiddenMiddle end

    abstract type Family{T} end
    abstract type Parent end

    struct Marker end
    struct DependentFamily{T,V<:AbstractVector{T}} end
end))
package_q = Core.eval(Base.__toplevel__, :(module PackagetypeTestQ
    struct Bar end
    struct Phantom{T} end
end))
Core.eval(package_q, :(struct ConcreteFoo <: $package_p.AbstractFoo end))
Core.eval(package_q, :(struct Hidden <: $package_p.Family{Union{}} end))
Core.eval(package_q, :(abstract type Middle <: $package_p.Parent end))
package_r = Core.eval(Base.__toplevel__, :(module PackagetypeTestR end))
Core.eval(package_r, :(struct Leaf <: $package_q.Middle end))
Core.eval(package_r, :(struct FamilyChild <: $package_p.Family{$package_q.Bar} end))

function has_package_type_portion(package_type, factors...)
    return any(package_type.alternatives) do portion
        length(portion.factors) == length(factors) &&
            all(factor -> any(candidate -> candidate === factor, portion.factors), factors)
    end
end

is_package_type_bottom(package_type) = isempty(package_type.alternatives)

@testset "package type exact unions" begin
    # Equal TypeNames do not imply overlap when invariant parameters differ.
    stable = Vector{Union{Vector{package_p.Foo},Vector{package_q.Bar}}}
    stable_result = Base.packagetype(stable)
    @test stable_result isa Base.PackagetypeExact
    @test has_package_type_portion(
        stable_result.value, Base, package_p, package_q)

    covariant_result = Base.packagetype(Union{package_p.Foo,package_q.Bar})
    @test covariant_result isa Base.PackagetypeExact
    @test has_package_type_portion(covariant_result.value, package_p)
    @test has_package_type_portion(covariant_result.value, package_q)

    bounded = Vector{T} where T<:package_p.AbstractFoo
    bounded_result = Base.packagetype(bounded)
    @test bounded_result isa Base.PackagetypeExact
    @test has_package_type_portion(bounded_result.value, Base, package_p)

    # An arm hidden by semantic subsumption must not contribute ownership.
    T = TypeVar(:T, Union{}, package_q.ConcreteFoo)
    U = TypeVar(:U, Union{}, package_p.AbstractFoo)
    redundant_union = UnionAll(T, UnionAll(U, Union{Ref{T},Ref{U}}))
    survivor = Ref{U} where U<:package_p.AbstractFoo
    @test redundant_union == survivor
    subsumed_result = Base.packagetype(Vector{redundant_union})
    @test subsumed_result isa Base.PackagetypeExact
    @test has_package_type_portion(subsumed_result.value, Base, package_p)

    # Overlapping arms with residuals are deliberately left to the stubbed solver.
    left = Pair{package_p.Foo,T} where T
    right = Pair{T,package_q.Bar} where T
    overlapping_result = Base.packagetype(Vector{Union{left,right}})
    @test overlapping_result isa Base.PackagetypeUnknown
    @test :overlapping_exact_union in
        getfield.(overlapping_result.diagnostics, :code)
    @test has_package_type_portion(
        overlapping_result.lower, Base, package_p, package_q)
    @test has_package_type_portion(overlapping_result.upper, Base, package_p)
    @test has_package_type_portion(overlapping_result.upper, Base, package_q)
end

@testset "package type supertype support" begin
    direct = Base.packagetype(package_q.ConcreteFoo)
    @test direct isa Base.PackagetypeExact
    @test has_package_type_portion(direct.value, package_q, package_p)

    transitive = Base.packagetype(package_r.Leaf)
    @test transitive isa Base.PackagetypeExact
    @test has_package_type_portion(
        transitive.value, package_r, package_q, package_p)

    parameterized = Base.packagetype(package_r.FamilyChild)
    @test parameterized isa Base.PackagetypeExact
    @test has_package_type_portion(
        parameterized.value, package_r, package_p, package_q)
end

@testset "package type parameter support" begin
    dependent = Base.packagetype(package_p.DependentFamily)
    @test dependent isa Base.PackagetypeExact
    @test has_package_type_portion(dependent.value, Base, package_p)

    exact_dependent_union = Vector{Union{T,package_p.Foo}} where T<:package_q.Bar
    exact_dependent_result = Base.packagetype(exact_dependent_union)
    @test exact_dependent_result isa Base.PackagetypeExact
    @test has_package_type_portion(
        exact_dependent_result.value, Base, package_p, package_q)

    covariant_dependent_union = Vector{T} where
        T<:Union{package_p.Foo,package_q.Bar}
    covariant_dependent_result = Base.packagetype(covariant_dependent_union)
    @test covariant_dependent_result isa Base.PackagetypeExact
    @test has_package_type_portion(
        covariant_dependent_result.value, Base, package_p)
    @test has_package_type_portion(
        covariant_dependent_result.value, Base, package_q)

    value_parameter = Base.packagetype(Val{package_p.Marker()})
    @test value_parameter isa Base.PackagetypeExact
    @test has_package_type_portion(value_parameter.value, Base, package_p)
end

@testset "package type productivity" begin
    bottom_result = Base.packagetype(Union{})
    @test bottom_result isa Base.PackagetypeExact
    @test is_package_type_bottom(bottom_result.value)

    empty_tuple_result = Base.packagetype(Tuple{})
    @test empty_tuple_result isa Base.PackagetypeExact
    @test is_package_type_bottom(empty_tuple_result.value)

    hidden_result = Base.packagetype(package_p.HiddenConcrete)
    @test hidden_result isa Base.PackagetypeExact
    @test is_package_type_bottom(hidden_result.value)

    hidden_leaf_result = Base.packagetype(package_p.HiddenLeaf)
    @test hidden_leaf_result isa Base.PackagetypeExact
    @test is_package_type_bottom(hidden_leaf_result.value)

    hidden_subtype_result = Base.packagetype(package_q.Hidden)
    @test hidden_subtype_result isa Base.PackagetypeExact
    @test is_package_type_bottom(hidden_subtype_result.value)

    # A semantically essential nonproductive arm poisons an exact union even
    # when an adjacent arm is productive.
    mixed_tuple = Base.packagetype(Vector{Union{Tuple{},package_p.Foo}})
    @test mixed_tuple isa Base.PackagetypeExact
    @test is_package_type_bottom(mixed_tuple.value)

    mixed_nominal = Base.packagetype(Vector{
        Union{package_q.Phantom{Union{}},package_p.Foo}})
    @test mixed_nominal isa Base.PackagetypeExact
    @test is_package_type_bottom(mixed_nominal.value)

    all_nonproductive = Base.packagetype(Vector{
        Union{Tuple{},package_q.Phantom{Union{}}}})
    @test all_nonproductive isa Base.PackagetypeExact
    @test is_package_type_bottom(all_nonproductive.value)

    vector_family = Vector{T} where T<:package_p.AbstractFoo
    redundant_nonproductive_arm = Base.packagetype(Vector{
        Union{Vector{Union{}},vector_family}})
    @test redundant_nonproductive_arm isa Base.PackagetypeExact
    @test has_package_type_portion(
        redundant_nonproductive_arm.value, Base, package_p)

    # Invariant unions expose the same poisoning through existential families.
    A = Vector{Union{T,String}} where T<:Vector{<:package_p.AbstractFoo}
    C = Vector{Union{Vector{Union{}},String}}
    @test C <: A
    c_result = Base.packagetype(C)
    @test c_result isa Base.PackagetypeExact
    @test is_package_type_bottom(c_result.value)

    hidden_A = Vector{Union{T,String}} where
        T<:package_p.Family{<:package_p.AbstractFoo}
    hidden_C = Vector{Union{package_q.Hidden,String}}
    @test hidden_C <: hidden_A
    hidden_c_result = Base.packagetype(hidden_C)
    @test hidden_c_result isa Base.PackagetypeExact
    @test is_package_type_bottom(hidden_c_result.value)

    # An unpinned existential bound is a covariant choice even though the
    # selected value becomes an exact nominal parameter in each witness.
    external_union = Pair{T,String} where
        T<:Union{Vector{Union{}},package_p.Foo}
    external_union_result = Base.packagetype(external_union)
    @test external_union_result isa Base.PackagetypeExact
    @test has_package_type_portion(
        external_union_result.value, Base, package_p)

    exact_union = Pair{
        Union{Vector{Union{}},package_p.Foo},
        String,
    }
    exact_union_result = Base.packagetype(exact_union)
    @test exact_union_result isa Base.PackagetypeExact
    @test is_package_type_bottom(exact_union_result.value)

    normalized_empty_tuple = Base.packagetype(NTuple{0,Int})
    @test NTuple{0,Int} === Tuple{}
    @test normalized_empty_tuple isa Base.PackagetypeExact
    @test is_package_type_bottom(normalized_empty_tuple.value)

    # In covariant position, a nonproductive arm contributes no witnesses, but
    # does not poison a productive sibling.
    covariant_mixed = Base.packagetype(Union{Tuple{},package_p.Foo})
    @test covariant_mixed isa Base.PackagetypeExact
    @test has_package_type_portion(covariant_mixed.value, package_p)

    productive_concrete_subtype = Base.packagetype(Union{
        Pair{Union{},package_p.Foo},
        Vector{package_p.Foo},
    })
    @test productive_concrete_subtype isa Base.PackagetypeExact
    @test has_package_type_portion(
        productive_concrete_subtype.value, Base, package_p)

    # An arm of unknown productivity cannot be replaced by package-type bottom:
    # it may add productive support absent from the known sibling.
    uncertain_bad = Pair{Union{},T} where T
    uncertain_good = Pair{T,package_p.Foo} where T
    uncertain_branch = Vector{Union{uncertain_bad,uncertain_good}}
    uncertain_result = Base.packagetype(uncertain_branch)
    @test uncertain_result isa Base.PackagetypeUnknown
    @test is_package_type_bottom(uncertain_result.lower)
    @test has_package_type_portion(
        uncertain_result.upper, Base, package_p)

    unknown_with_productive_sibling = Base.packagetype(Union{
        uncertain_branch,
        Vector{package_q.Bar},
    })
    @test unknown_with_productive_sibling isa Base.PackagetypeUnknown
    @test has_package_type_portion(
        unknown_with_productive_sibling.lower, Base, package_q)
    @test has_package_type_portion(
        unknown_with_productive_sibling.upper, Base, package_p)
    @test has_package_type_portion(
        unknown_with_productive_sibling.upper, Base, package_q)

    variable_tail = Base.packagetype(Tuple{Vararg{package_q.Bar}})
    @test variable_tail isa Base.PackagetypeExact
    @test has_package_type_portion(variable_tail.value, Base, package_q)

    fixed_prefix = Base.packagetype(Tuple{Int,Vararg{package_q.Bar}})
    @test fixed_prefix isa Base.PackagetypeExact
    @test has_package_type_portion(fixed_prefix.value, Base)

    variable_length = Base.packagetype(NTuple{N,package_q.Bar} where N)
    @test variable_length isa Base.PackagetypeExact
    @test has_package_type_portion(variable_length.value, Base, package_q)

    variable_length_tail = Base.packagetype(
        Tuple{Int,Vararg{package_q.Bar,N}} where N)
    @test variable_length_tail isa Base.PackagetypeExact
    @test has_package_type_portion(variable_length_tail.value, Base)

    type_family = Base.packagetype(Type{T} where T)
    @test type_family isa Base.PackagetypeExact
    @test has_package_type_portion(type_family.value, Base)
end
