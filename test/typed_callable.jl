# This file is a part of Julia. License is MIT: https://julialang.org/license

# Tests for Core.TypedCallable: a concretely-typed callable that dispatches its
# wrapped callable in the *latest* world (re-resolving on method redefinition),
# the runtime analog of @cfunction (contrast OpaqueClosure's frozen world).
using Test
using Base.Experimental: @opaque

tc_add1(x) = x + 1

@testset "construction and basic call" begin
    tc = Core.TypedCallable{Tuple{Int},Int}(tc_add1)
    @test tc isa Core.TypedCallable{Tuple{Int},Int}
    # specsig fast path: a concretely-typed caller reaches the target without boxing
    caller(t::Core.TypedCallable{Tuple{Int},Int}) = t(5)
    @test caller(tc) === 6
    # boxed/jlcall path: @nospecialize forces dynamic dispatch through the builtin
    dyn(@nospecialize(t), x) = t(x)
    @test dyn(tc, 5) === 6
    # A must be a Tuple type
    @test_throws ArgumentError Core.TypedCallable{Int,Int}(tc_add1)
end

@testset "latest-world re-resolution" begin
    @eval lw_g(x) = x + 1
    tc = Core.TypedCallable{Tuple{Int},Int}(lw_g)
    cg(t::Core.TypedCallable{Tuple{Int},Int}) = t(10)
    @test cg(tc) === 11
    # Redefining a covered method advances the world; the call reaches the new method.
    @eval lw_g(x) = x + 100
    @test cg(tc) === 110
    # Contrast: an OpaqueClosure freezes the construction-time world.
    @eval oc_g(x) = x + 1
    oc = @opaque (x::Int) -> oc_g(x)
    @test oc(10) === 11
    @eval oc_g(x) = x + 100
    @test oc(10) === 11
end

@testset "vararg" begin
    tc_sum(xs...) = sum(xs)
    tc = Core.TypedCallable{Tuple{Vararg{Int}},Int}(tc_sum)
    cv(t::Core.TypedCallable{Tuple{Vararg{Int}},Int}) = t(1, 2, 3, 4)
    @test cv(tc) === 10
    @test tc(1, 2, 3) === 6
end

@testset "type enforcement" begin
    tc_bad(x) = "not an int"
    tc = Core.TypedCallable{Tuple{Int},Int}(tc_bad)
    # Return type R is enforced on both the specsig and the jlcall path.
    cbad(t::Core.TypedCallable{Tuple{Int},Int}) = t(1)
    @test_throws TypeError cbad(tc)
    dynbad(@nospecialize(t)) = t(1)
    @test_throws TypeError dynbad(tc)
    # Argument types are checked on the jlcall path.
    tcok = Core.TypedCallable{Tuple{Int},Int}(tc_add1)
    dynarg(@nospecialize(t), @nospecialize(x)) = t(x)
    @test_throws TypeError dynarg(tcok, "x")
    # Wrong arity errors.
    @test_throws MethodError dynarg(tcok, 1, 2)
end

@testset "inference" begin
    # Calling a TypedCallable{A,R} infers the return type R.
    caller(t::Core.TypedCallable{Tuple{Int},Int}) = t(5)
    @test Base.return_types(caller, (Core.TypedCallable{Tuple{Int},Int},)) == Any[Int]
    callerf(t::Core.TypedCallable{Tuple{Int},Float64}) = t(1)
    @test Base.return_types(callerf, (Core.TypedCallable{Tuple{Int},Float64},)) == Any[Float64]
end

@testset "trampoline sharing" begin
    # Two TypedCallables over the same (typeof(f), A, R) share one canonical
    # trampoline record from the `Core.dispatch_trampolines` cache; a different
    # (A, R) gets its own record. Field 2 is the hidden trampoline field.
    share_f(x) = x + 1
    a = Core.TypedCallable{Tuple{Int},Int}(share_f)
    b = Core.TypedCallable{Tuple{Int},Int}(share_f)
    @test getfield(a, 2) === getfield(b, 2)
    @test getfield(a, 2) isa Core.DispatchTrampoline
    c = Core.TypedCallable{Tuple{Int},Float64}(share_f)
    @test getfield(c, 2) !== getfield(a, 2)
    # A @cfunction over the same resolution sig uses a distinct record: the
    # trampoline key includes the ABI kind (STD vs TypedCallable).
    std_tr = ccall(:jl_get_dispatch_trampoline, Any, (Any, Any, Cint, Cint),
                   Tuple{typeof(share_f), Int}, Int, Cint(1), Cint(0))
    @test std_tr !== getfield(a, 2)
end
