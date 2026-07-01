// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "julia.h"
#include "julia_internal.h"

// Process-global cache backing `jl_dispatch_trampolines` (the `Core.dispatch_trampolines`
// singleton). See the section comment below for the cache structure.

// ---- dispatch-trampoline cache (@cfunction/@ccallable) ----
// Maps (sigt, rt, specsig) -> jl_dispatch_trampoline_t, keyed on the resolution sig `sigt` =
// `Tuple{typeof(f), A...}` alone. Records sharing a `sigt` (differing in `rt` or `specsig`) are
// chained through `jl_dispatch_trampoline_t.next` and disambiguated by (rt, specsig).

static jl_dispatch_trampoline_t *tramp_alloc_entry(jl_task_t *ct, jl_value_t *sigt, jl_value_t *rt,
                                          int specsig) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = (jl_dispatch_trampoline_t*)jl_gc_alloc(ct->ptls, sizeof(jl_dispatch_trampoline_t), jl_dispatch_trampoline_type);
    e->sigt = sigt;
    e->rt = rt;
    e->last_invokee = NULL; // unresolved
    jl_atomic_store_relaxed(&e->fptr, (void*)NULL);
    jl_atomic_store_relaxed(&e->last_world, (size_t)0);
    jl_atomic_store_relaxed(&e->next, (jl_dispatch_trampoline_t*)NULL);
    e->specsig = specsig ? 1 : 0;
    return e;
}

// Record key within a `sigt` bucket; the fields live packed inline on the record itself.
typedef struct {
    jl_value_t *rt;
    int specsig;
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
        && (e->rt == k->rt || jl_types_equal(e->rt, k->rt));
}

// Lock-free lookup of the trampoline for (sigt, rt, specsig); NULL if absent. Safe to call
// with or without the writelock held.
static jl_dispatch_trampoline_t *tramp_map_lookup(jl_value_t *sigt, jl_value_t *rt, int specsig) JL_CANSAFEPOINT
{
    tramp_key_t key = { rt, specsig };
    return (jl_dispatch_trampoline_t*)jl_typemap_list_lookup(&jl_dispatch_trampolines->cache,
            sigt, offsetof(jl_dispatch_trampoline_t, next), tramp_match, &key);
}

// Insert `tr` into the `sigt`-keyed bucket. Caller holds the writelock and must have
// confirmed (under the lock) that (sigt, rt, specsig) is absent; `sigt`/`tr` must be kept
// rooted.
static void tramp_map_insert(jl_value_t *sigt, jl_dispatch_trampoline_t *tr) JL_CANSAFEPOINT
{
    jl_typemap_list_insert(&jl_dispatch_trampolines->cache, (jl_value_t*)jl_dispatch_trampolines,
            sigt, (jl_value_t*)tr, offsetof(jl_dispatch_trampoline_t, next));
}

// Get (or create) the canonical @cfunction/@ccallable dispatch trampoline for
// (sigt, rt, specsig); call sites with the same key share one trampoline. Caller must root
// `sigt`/`rt`.
JL_DLLEXPORT jl_dispatch_trampoline_t *jl_get_dispatch_trampoline(jl_value_t *sigt, jl_value_t *rt, int specsig) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = NULL;
    JL_GC_PUSH1(&e);
    e = tramp_map_lookup(sigt, rt, specsig); // lock-free fast path
    if (e == NULL) {
        JL_LOCK(&jl_dispatch_trampolines->writelock);
        e = tramp_map_lookup(sigt, rt, specsig); // re-check: another thread may have inserted
        if (e == NULL) {
            e = tramp_alloc_entry(jl_current_task, sigt, rt, specsig);
            tramp_map_insert(sigt, e);
        }
        JL_UNLOCK(&jl_dispatch_trampolines->writelock);
    }
    JL_GC_POP();
    return e;
}

// Insert `tr` into the running cache if its key is absent and return the canonical record;
// keep-first, like jl_specializations_get_or_insert (a losing `tr` is left standalone). Used
// by the load fixup to re-insert image-restored trampolines.
JL_DLLEXPORT jl_dispatch_trampoline_t *jl_insert_dispatch_trampoline(jl_dispatch_trampoline_t *tr) JL_CANSAFEPOINT
{
    jl_dispatch_trampoline_t *e = NULL;
    JL_GC_PUSH2(&tr, &e);
    JL_LOCK(&jl_dispatch_trampolines->writelock);
    e = tramp_map_lookup(tr->sigt, tr->rt, tr->specsig);
    if (e == NULL) {
        tramp_map_insert(tr->sigt, tr);
        e = tr;
    }
    JL_UNLOCK(&jl_dispatch_trampolines->writelock);
    JL_GC_POP();
    return e;
}
