// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "julia.h"
#include "julia_internal.h"
#include "builtin_proto.h"

// TypedCallable{A,R}: a concretely-typed callable wrapping a callable `f`,
// dispatched in the *latest* world (contrast OpaqueClosure's frozen world).
// The target is monomorphic in the construction-time signature
// `Tuple{typeof(f), A...}` -- there is no runtime-argument-based dispatch.
//
// Each instance holds a shared dispatch trampoline record (`tc->trampoline`,
// from the `Core.dispatch_trampolines` cache, keyed on (sigt, rt, specsig=1,
// kind=JL_ABI_TYPED_CALLABLE)). The record caches, per latest world, the
// resolved target and a specsig adapter for the erased-slot-0 call ABI, for
// use by the inline specsig call site (jl_update_dispatch_trampoline in
// runtime_ccall.c). The jlcall builtin below is the boxed slow path and
// dispatches `tc->f` directly via `jl_apply_generic`.

// Build the ABI-adapter signature for a TypedCallable trampoline. The adapter is
// invoked with the `TypedCallable{argt,rt}` wrapper itself in slot 0 (type-erased;
// it recovers `tc->f` internally). So its signature is
// `Tuple{TypedCallable{argt,rt}, argt...}`, distinct from the trampoline's
// dispatch signature `tramp_sigt = Tuple{typeof(f), argt...}` (which is only used
// to resolve the target). Used by the adapter emitters in aotcompile.cpp (AOT)
// and runtime_ccall.c (JIT resolve).
JL_DLLEXPORT jl_value_t *jl_typed_callable_adapter_sigt(jl_value_t *tramp_sigt, jl_value_t *rt) JL_CANSAFEPOINT
{
    jl_value_t *argt = NULL;
    jl_value_t *tc_type = NULL;
    jl_value_t *adapter_sigt = NULL;
    JL_GC_PUSH3(&argt, &tc_type, &adapter_sigt);
    argt = jl_argtype_without_function(tramp_sigt); // Tuple{argt...}
    tc_type = jl_apply_type2((jl_value_t*)jl_typed_callable_type, argt, rt); // TypedCallable{argt,rt}
    adapter_sigt = jl_argtype_with_function_type(tc_type, argt); // Tuple{TypedCallable{argt,rt}, argt...}
    JL_GC_POP();
    return adapter_sigt;
}

// Construct a `TypedCallable{argt,rt}` wrapping `f`. If `tr != NULL` it is used as
// the dispatch trampoline directly (the optimized 4-arg builtin form: the optimizer
// resolved it at compile time, so the runtime cache lookup is skipped); otherwise
// the trampoline is obtained by (sigt, rt) key -- an image-serialized, re-inserted
// record is reused, no runtime JIT.
static jl_typed_callable_t *typed_callable_construct(jl_task_t *ct, jl_value_t *f,
        jl_tupletype_t *argt, jl_value_t *rt, jl_dispatch_trampoline_t *tr) JL_CANSAFEPOINT
{
    jl_value_t *sigt = NULL;
    jl_value_t *tc_type = NULL;
    JL_GC_PUSH3(&sigt, &tc_type, &tr);
    if (tr == NULL) {
        sigt = jl_argtype_with_function(f, (jl_value_t*)argt); // Tuple{typeof(f), A...}
        tr = jl_get_dispatch_trampoline(sigt, rt, /*specsig*/1, JL_ABI_TYPED_CALLABLE);
    }
    tc_type = jl_apply_type2((jl_value_t*)jl_typed_callable_type, (jl_value_t*)argt, rt);
    jl_typed_callable_t *tc = (jl_typed_callable_t*)jl_gc_alloc(ct->ptls, sizeof(jl_typed_callable_t), tc_type);
    tc->f = f;
    tc->trampoline = (jl_value_t*)tr;
    JL_GC_POP();
    return tc;
}

JL_DLLEXPORT jl_typed_callable_t *jl_new_typed_callable(jl_value_t *f, jl_tupletype_t *argt, jl_value_t *rt) JL_CANSAFEPOINT
{
    if (!jl_is_tuple_type((jl_value_t*)argt))
        jl_error("TypedCallable argument tuple must be a tuple type");
    JL_TYPECHK(TypedCallable, type, rt);
    return typed_callable_construct(jl_current_task, f, argt, rt, /*tr*/NULL);
}

// 4-arg builtin form: the trampoline was resolved by the optimizer and is supplied
// directly.
JL_DLLEXPORT jl_typed_callable_t *jl_new_typed_callable_resolved(jl_dispatch_trampoline_t *tr,
        jl_value_t *f, jl_tupletype_t *argt, jl_value_t *rt) JL_CANSAFEPOINT
{
    if (!jl_is_tuple_type((jl_value_t*)argt))
        jl_error("TypedCallable argument tuple must be a tuple type");
    JL_TYPECHK(TypedCallable, type, rt);
    return typed_callable_construct(jl_current_task, f, argt, rt, tr);
}

// Builtin constructor `Core._typed_callable(f, A, R)`: the surface
// `Core.TypedCallable{A,R}(f)` lowers to this so the optimizer can see the
// construction site (infer its `TypedCallable{A,R}` type and, for --trim, discover
// the dispatched target via collectinvokes!). It does not freeze a resolved
// CodeInstance: the target is always dispatched in the latest world through the
// trampoline.
JL_CALLABLE(jl_f__typed_callable) JL_CANSAFEPOINT
{
    JL_NARGS(_typed_callable, 3, 4);
    if (nargs == 4) {
        // Optimized form `(trampoline, f, A, R)`: the optimizer resolved the
        // dispatch trampoline at compile time (see the inlining transform), so the
        // construction uses it directly rather than looking it up in the cache.
        if (!jl_typetagis(args[0], jl_dispatch_trampoline_type))
            jl_type_error("_typed_callable", (jl_value_t*)jl_dispatch_trampoline_type, args[0]);
        return (jl_value_t*)jl_new_typed_callable_resolved((jl_dispatch_trampoline_t*)args[0], args[1],
                (jl_tupletype_t*)args[2], args[3]);
    }
    return (jl_value_t*)jl_new_typed_callable(args[0], (jl_tupletype_t*)args[1], args[2]);
}

// Builtin (jlcall) call: typecheck args against the declared argt, then dispatch
// `tc->f` in the latest world.  This is the boxed/slow path -- callers arrive
// here through dynamic dispatch already, so a plain `jl_apply_generic` at the
// latest world is the natural target.  (Specsig callers instead reach the target
// through the shared trampoline `fptr`; see the inline call site in codegen.)
// Mirrors `jl_f_opaque_closure_call`'s typecheck, but the world is "latest".
JL_CALLABLE(jl_f_typed_callable_call) JL_CANSAFEPOINT
{
    jl_typed_callable_t *tc = (jl_typed_callable_t*)F;
    jl_value_t *argt = jl_tparam0(jl_typeof(tc));
    if (!jl_tupletype_length_compat(argt, nargs))
        jl_method_error(F, args, nargs + 1, jl_atomic_load_acquire(&jl_world_counter));
    argt = jl_unwrap_unionall(argt);
    assert(jl_is_datatype(argt));
    jl_svec_t *types = jl_get_fieldtypes((jl_datatype_t*)argt);
    size_t ntypes = jl_svec_len(types);
    for (int i = 0; i < nargs; ++i) {
        jl_value_t *typ = i >= ntypes ? jl_svecref(types, ntypes-1) : jl_svecref(types, i);
        if (jl_is_vararg(typ))
            typ = jl_unwrap_vararg(typ);
        jl_typeassert(args[i], typ);
    }
    jl_task_t *ct = jl_current_task;
    size_t last_age = ct->world_age;
    ct->world_age = jl_atomic_load_acquire(&jl_world_counter);
    jl_value_t *res = jl_apply_generic(tc->f, args, nargs);
    ct->world_age = last_age;
    // Enforce the declared return type R, matching the specsig adapter (which
    // type-asserts the result against `rt`).  `R` is the second type parameter.
    jl_value_t *rt = jl_tparam1(jl_typeof(tc));
    jl_typeassert(res, rt);
    return res;
}
