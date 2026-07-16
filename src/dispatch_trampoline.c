// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "julia.h"
#include "julia_internal.h"

// Process-global cache backing `jl_dispatch_trampolines` (the `Core.dispatch_trampolines`
// singleton). See the section comment below for the cache structure.

// ---- dispatch-trampoline cache (@cfunction/@ccallable) ----
// Maps (sigt, rt, specsig, kind) -> jl_dispatch_trampoline_t, keyed on the resolution sig `sigt` =
// `Tuple{typeof(f), A...}` alone. Records sharing a `sigt` (differing in `rt`, `specsig`, or
// `kind`) are chained through `jl_dispatch_trampoline_t.next` and disambiguated by
// (rt, specsig, kind).

static jl_dispatch_trampoline_t *tramp_alloc_entry(jl_task_t *ct, jl_value_t *sigt, jl_value_t *rt,
                                          int specsig, jl_adapter_kind_t kind) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = (jl_dispatch_trampoline_t*)jl_gc_alloc(ct->ptls, sizeof(jl_dispatch_trampoline_t), jl_dispatch_trampoline_type);
    e->sigt = sigt;
    e->rt = rt;
    e->last_invokee = NULL; // unresolved
    jl_atomic_store_relaxed(&e->fptr, (void*)NULL);
    jl_atomic_store_relaxed(&e->last_world, (size_t)0);
    jl_atomic_store_relaxed(&e->next, (jl_dispatch_trampoline_t*)NULL);
    e->specsig = specsig ? 1 : 0;
    e->kind = (uint8_t)kind;
    return e;
}

// Record key within a `sigt` bucket; the fields live packed inline on the record itself.
typedef struct {
    jl_value_t *rt;
    int specsig;
    jl_adapter_kind_t kind;
} tramp_key_t;

// `rt` is compared by *type equality* (jl_types_equal), matching how the TypeMap matches
// `sigt`; `jl_egal` would split type-equal-but-not-egal return types into duplicate records.
// `specsig` is part of the key because uses_specsig depends on the emitting cgparams
// (prefer_specsig), not just (sigt, rt); a call site must get a record built for its own
// calling convention.
static int tramp_match(jl_value_t *rec, void *keyv) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = (jl_dispatch_trampoline_t*)rec;
    tramp_key_t *k = (tramp_key_t*)keyv;
    return (int)e->specsig == (k->specsig ? 1 : 0)
        && (jl_adapter_kind_t)e->kind == k->kind
        && (e->rt == k->rt || jl_types_equal(e->rt, k->rt));
}

// Lock-free lookup of the trampoline for (sigt, rt, specsig, kind); NULL if absent. Safe to
// call with or without the writelock held.
static jl_dispatch_trampoline_t *tramp_map_lookup(jl_value_t *sigt, jl_value_t *rt, int specsig, jl_adapter_kind_t kind) JL_CANSAFEPOINT
{
    tramp_key_t key = { rt, specsig, kind };
    return (jl_dispatch_trampoline_t*)jl_typemap_list_lookup(&jl_dispatch_trampolines->cache,
            sigt, offsetof(jl_dispatch_trampoline_t, next), tramp_match, &key);
}

// Insert `tr` into the `sigt`-keyed bucket. Caller holds the writelock and must have
// confirmed (under the lock) that (sigt, rt, specsig, kind) is absent; `sigt`/`tr` must be kept
// rooted.
static void tramp_map_insert(jl_value_t *sigt, jl_dispatch_trampoline_t *tr) JL_CANSAFEPOINT
{
    jl_typemap_list_insert(&jl_dispatch_trampolines->cache, (jl_value_t*)jl_dispatch_trampolines,
            sigt, (jl_value_t*)tr, offsetof(jl_dispatch_trampoline_t, next));
}

// Get (or create) the canonical @cfunction/@ccallable dispatch trampoline for
// (sigt, rt, specsig, kind); call sites with the same key share one trampoline. Caller must
// root `sigt`/`rt`.
JL_DLLEXPORT jl_dispatch_trampoline_t *jl_get_dispatch_trampoline(jl_value_t *sigt, jl_value_t *rt, int specsig, jl_adapter_kind_t kind) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = NULL;
    JL_GC_PUSH1(&e);
    e = tramp_map_lookup(sigt, rt, specsig, kind); // lock-free fast path
    if (e == NULL) {
        JL_LOCK(&jl_dispatch_trampolines->writelock);
        e = tramp_map_lookup(sigt, rt, specsig, kind); // re-check: another thread may have inserted
        if (e == NULL) {
            e = tramp_alloc_entry(jl_current_task, sigt, rt, specsig, kind);
            tramp_map_insert(sigt, e);
        }
        JL_UNLOCK(&jl_dispatch_trampolines->writelock);
    }
    JL_GC_POP();
    return e;
}


// Walk the whole `sigt` bucket chain: rt/specsig/kind variants share one TypeMap entry,
// so pushing only the head would miss them. Called under the writelock (relaxed loads).
static int tramp_collect_visitor(jl_typemap_entry_t *e, void *closure) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *tr = (jl_dispatch_trampoline_t*)jl_atomic_load_relaxed((_Atomic(jl_value_t*)*)&e->func.value);
    for (; tr != NULL; tr = jl_atomic_load_relaxed(&tr->next))
        jl_array_ptr_1d_push((jl_array_t*)closure, (jl_value_t*)tr);
    return 1;
}

// Snapshot every record in the cache (all kinds) into a fresh Vector{Any}. Takes the
// writelock only for the walk. Used by the --trim build to seed adapter emission for
// trampolines created by build-time *execution* (e.g. a top-level TypedCallable
// construction), which never appear in compiled code.
JL_DLLEXPORT jl_value_t *jl_collect_dispatch_trampolines(void) JL_CANSAFEPOINT
{
    jl_array_t *out = jl_alloc_vec_any(0);
    JL_GC_PUSH1(&out);
    JL_LOCK(&jl_dispatch_trampolines->writelock);
    jl_typemap_t *map = jl_atomic_load_relaxed(&jl_dispatch_trampolines->cache);
    if ((jl_value_t*)map != jl_nothing)
        jl_typemap_visitor(map, tramp_collect_visitor, (void*)out);
    JL_UNLOCK(&jl_dispatch_trampolines->writelock);
    JL_GC_POP();
    return (jl_value_t*)out;
}

// Insert `tr` into the running cache if its key is absent and return the canonical record;
// keep-first, like jl_specializations_get_or_insert (a losing `tr` is left standalone). Used
// by the load fixup to re-insert image-restored trampolines.
JL_DLLEXPORT jl_dispatch_trampoline_t *jl_insert_dispatch_trampoline(jl_dispatch_trampoline_t *tr) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = NULL;
    JL_GC_PUSH2(&tr, &e);
    JL_LOCK(&jl_dispatch_trampolines->writelock);
    e = tramp_map_lookup(tr->sigt, tr->rt, tr->specsig, (jl_adapter_kind_t)tr->kind);
    if (e == NULL) {
        tramp_map_insert(tr->sigt, tr);
        e = tr;
    }
    JL_UNLOCK(&jl_dispatch_trampolines->writelock);
    JL_GC_POP();
    return e;
}
