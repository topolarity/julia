// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "julia.h"
#include "julia_internal.h"

// Process-global cache backing `jl_abi_adapters` (the `Core.abi_adapters` singleton).
// See the section comment below for the cache / bucket structure.

// ---- ABI adapter cache (`jl_abi_adapters->cache`) ----
// A TypeMap keyed on the adapter `sigt` alone (its
// slot 0 is the function type, never `Union{}`). Each TypeMap entry holds a *bucket* of
// jl_abi_adapter_t records that share one `sigt` but differ in (rt, ci, specsig,
// kind, nargs). Because an adapter `sigt` may be shared by many distinct target
// `ci`, the bucket is adaptive, mirroring the TypeMap's own single/list/cache trichotomy:
//   tier 1-2: `entry->func.value` is a `.next`-chained list of records (kept while
//             count <= MAX_ADAPTER_LIST_COUNT); appended at the tail so the head
//             never moves and readers walk it lock-free;
//   tier 3:   promoted to a `jl_eqtable` (Memory) keyed on the record's `ci`
//             (NULL -> jl_nothing), whose value is a short `.next` chain of the
//             same-ci variants.
// `entry->func.value` is read with acquire / written with release (it is swapped on
// promotion), so lock-free readers see a complete old-or-new representation. A reader
// mid-walk during promotion may spuriously miss and must recover via a writelock-held
// recheck (jl_lookup_abi_converter). The record lists are jl_typemap_list_t (typemap.c); the
// eqtable tiering is local to this cache. The JIT half (LLVM emit + record allocation)
// lives in jitlayers.cpp.

#define MAX_ADAPTER_LIST_COUNT 6 // mirror MAX_METHLIST_COUNT: promote chain -> eqtable above this

// Record key within a `sigt` bucket; the fields live packed inline on the record itself.
typedef struct {
    jl_value_t *rt;
    jl_code_instance_t *ci;
    int specsig;
    jl_abi_kind_t kind;
    size_t nargs;
} abi_adapter_key_t;

// `rt` is compared by *type equality* (jl_types_equal), mirroring the TypeMap's `sigt` match;
// jl_egal would split type-equal-but-not-egal return types into duplicate records.
static int abi_adapter_match(jl_value_t *rec, void *keyv) JL_CANSAFEPOINT
{
    jl_abi_adapter_t *e = (jl_abi_adapter_t*)rec;
    abi_adapter_key_t *k = (abi_adapter_key_t*)keyv;
    return e->ci == k->ci
        && (int)e->specsig == (k->specsig ? 1 : 0)
        && (jl_abi_kind_t)e->kind == k->kind
        && e->nargs == k->nargs
        && (e->rt == k->rt || jl_types_equal(e->rt, k->rt)); // rt lives in the bucket (key is sigt alone)
}

// eqtable key for a record's `ci` (eqtable can't key NULL -> jl_nothing sentinel).
static jl_value_t *abi_adapter_cikey(jl_code_instance_t *ci) JL_NOTSAFEPOINT
{
    return ci ? (jl_value_t*)ci : jl_nothing;
}

// Find a record in `te`'s bucket. `repr` (acquire) is either a record list (tiers 1-2) or a
// `ci`-keyed eqtable of record lists (tier 3); both reduce to a short list walk.
static jl_abi_adapter_t *abi_adapter_bucket_find(jl_typemap_entry_t *te, abi_adapter_key_t *key) JL_CANSAFEPOINT
{
    jl_value_t *repr = jl_atomic_load_acquire((_Atomic(jl_value_t*)*)&te->func.value);
    if (repr == NULL)
        return NULL;
    jl_typemap_list_t *head = repr;
    if (jl_is_genericmemory(repr))
        head = jl_eqtable_get((jl_genericmemory_t*)repr, abi_adapter_cikey(key->ci), NULL);
    return (jl_abi_adapter_t*)jl_typemap_list_find(head, offsetof(jl_abi_adapter_t, next),
            abi_adapter_match, key);
}

// Whether a target entry point of kind `api` (belonging to `mi`, returning `rettype`)
// already satisfies the caller ABI `from_abi`, so no wrapping adapter is needed. The AOT path
// passes the api of the Function it emitted (decls.invoke_api); the runtime derives it from
// the published entry points (abi_adapter_resolve_target).
JL_DLLEXPORT int jl_abi_matches_invoke_api(jl_abi_t from_abi, jl_invoke_api_t api,
        jl_method_instance_t *mi, jl_value_t *rettype) JL_CANSAFEPOINT
{
    // A non-STD caller ABI can never be satisfied by the target's own entry point:
    // the kind obliges the adapter to perform a call-frame conversion (e.g. OC->STD
    // world switch + captures unpack) that the raw target does not do.
    if (from_abi.kind != JL_ABI_STD)
        return 0;
    if (api == JL_INVOKE_ARGS)
        return !from_abi.specsig && jl_subtype(rettype, from_abi.rt);
    if (api == JL_INVOKE_SPECSIG)
        return from_abi.specsig && jl_egal(mi->specTypes, from_abi.sigt) && jl_egal(rettype, from_abi.rt);
    return 0;
}

// Resolve whether (`from_abi`, `codeinst`) needs a wrapping adapter at all. If the target's
// own compiled entry point already satisfies the requested ABI, return that specptr directly
// (no adapter). Otherwise return NULL and fill *target / *target_specsig / *invoke describing
// the target the adapter must bridge to. Pure metadata resolution: no codegen and no
// compilation, so it is also usable in builds without codegen.
static void *abi_adapter_resolve_target(jl_abi_t from_abi, jl_code_instance_t *codeinst,
        void **target, int *target_specsig, jl_callptr_t *invoke) JL_CANSAFEPOINT
{
    *target = NULL;
    *target_specsig = 0;
    *invoke = NULL;
    if (codeinst == NULL)
        return NULL;
    uint8_t specsigflags;
    jl_method_instance_t *mi = jl_get_ci_mi(codeinst);
    void *specptr = NULL;
    jl_callptr_t inv = NULL;
    // `waitcompile` must be 0 to keep this callable without codegen. A target still
    // mid-compilation reads back as `inv == NULL`: no shortcut.
    jl_read_codeinst_invoke(codeinst, &specsigflags, &inv, &specptr, /* waitcompile */ 0);
    *invoke = inv;
    if (inv == NULL)
        return NULL;
    if (inv == jl_fptr_const_return_addr) {
        // const-return has no specptr to shortcut to: an adapter is always required.
        return NULL;
    }
    else if (inv == jl_fptr_args_addr) {
        assert(specptr != NULL);
        if (jl_abi_matches_invoke_api(from_abi, JL_INVOKE_ARGS, mi, codeinst->rettype))
            return specptr; // no adapter required
        *target = specptr;
        *target_specsig = 0;
    }
    else if (specsigflags & JL_CI_FLAGS_SPECPTR_SPECIALIZED) {
        assert(specptr != NULL);
        if (jl_abi_matches_invoke_api(from_abi, JL_INVOKE_SPECSIG, mi, codeinst->rettype))
            return specptr; // no adapter required
        *target = specptr;
        *target_specsig = 1;
    }
    return NULL;
}

// The target's own compiled entry point when it already satisfies `from_abi` (so no adapter
// is needed), else NULL. Pure metadata read; usable without codegen.
JL_DLLEXPORT void *jl_abi_matching_specptr(jl_abi_t from_abi, jl_code_instance_t *codeinst) JL_CANSAFEPOINT
{
    void *target;
    int target_specsig;
    jl_callptr_t invoke;
    return abi_adapter_resolve_target(from_abi, codeinst, &target, &target_specsig, &invoke);
}

// Lock-free lookup of the adapter record for (sigt, rt, ci, specsig, kind,
// nargs). Returns the record or NULL. Safe to call with or without the writelock held.
JL_DLLEXPORT jl_abi_adapter_t *jl_lookup_abi_adapter(jl_value_t *sigt, jl_value_t *rt,
        jl_code_instance_t *ci, int specsig, jl_abi_kind_t kind, size_t nargs) JL_CANSAFEPOINT
{
    // Key on `sigt` alone (its slot 0 is the function type, never Union{}); the remaining
    // fields are disambiguated in the bucket (abi_adapter_match).
    abi_adapter_key_t key = { rt, ci, specsig, kind, nargs };
    jl_typemap_entry_t *te = jl_typemap_list_entry(&jl_abi_adapters->cache, sigt);
    if (te == NULL)
        return NULL;
    return abi_adapter_bucket_find(te, &key);
}

// Find a callable adapter fptr for (from_abi, codeinst) without JITing: the target's own
// specptr when its compiled ABI already matches, else a cached record. A lock-free
// miss is re-checked under the writelock (a concurrent bucket promotion can cause a spurious
// miss; see the section comment above). Returns NULL when no adapter exists: the JIT path
// then compiles one, and a codegen-free caller can re-query with codeinst == NULL for the
// signature's dynamic-dispatch adapter. All out parameters are optional: `invokee` receives
// the Union{CodeInstance, ABIAdapter} behind the returned fptr; the rest receive the
// resolve-target results for a caller that proceeds to JIT.
JL_DLLEXPORT void *jl_lookup_abi_converter(jl_abi_t from_abi, jl_code_instance_t *codeinst,
        void **target, int *target_specsig, jl_callptr_t *invoke, jl_value_t **invokee) JL_CANSAFEPOINT
{
    void *tgt = NULL;
    int ts = 0;
    jl_callptr_t inv = NULL;
    if (invokee)
        *invokee = NULL;
    void *shortcut = abi_adapter_resolve_target(from_abi, codeinst, &tgt, &ts, &inv);
    if (target)
        *target = tgt;
    if (target_specsig)
        *target_specsig = ts;
    if (invoke)
        *invoke = inv;
    if (shortcut != NULL) {
        if (invokee)
            *invokee = (jl_value_t*)codeinst; // bare CI: no adapter record required
        return shortcut;
    }
    jl_abi_adapter_t *e = jl_lookup_abi_adapter(from_abi.sigt, from_abi.rt, codeinst,
            from_abi.specsig, from_abi.kind, from_abi.nargs);
    if (e == NULL || e->fptr == NULL) {
        JL_LOCK(&jl_abi_adapters->writelock);
        e = jl_lookup_abi_adapter(from_abi.sigt, from_abi.rt, codeinst,
                from_abi.specsig, from_abi.kind, from_abi.nargs);
        JL_UNLOCK(&jl_abi_adapters->writelock);
    }
    // A record without a compiled thunk (fptr == NULL) cannot be served; report a miss so the
    // caller JITs one (jl_get_abi_adapter fills such a record in place) or errors cleanly.
    if (e == NULL || e->fptr == NULL)
        return NULL;
    if (invokee)
        *invokee = (jl_value_t*)e;
    return e->fptr;
}

// Insert `e` (with `e->next` published via release) into `tbl`'s `ci`-bucket chain by
// prepending. Returns the (possibly reallocated) table.
static jl_genericmemory_t *abi_adapter_eqtable_prepend(jl_genericmemory_t *tbl, jl_abi_adapter_t *e) JL_CANSAFEPOINT
{
    jl_value_t *cik = abi_adapter_cikey(e->ci);
    jl_abi_adapter_t *head = (jl_abi_adapter_t*)jl_eqtable_get(tbl, cik, NULL);
    // `e` may be an old-gen record (promotion regroups existing chain records;
    // get-or-insert adds in-image records), so the new e -> head edge needs the write barrier.
    jl_gc_write_atomic(e, e->next, jl_abi_adapter_t, head, release);
    int inserted = 0;
    return jl_eqtable_put(tbl, cik, (jl_value_t*)e, &inserted);
}

// Insert `entry` into the adapters cache. Caller holds the writelock and must have
// confirmed (under the lock) that the key is absent.
static void abi_adapter_insert(jl_abi_adapter_t *entry) JL_CANSAFEPOINT
{
    jl_genericmemory_t *tbl = NULL;
    jl_abi_adapter_t *e = NULL, *nxt = NULL;
    JL_GC_PUSH4(&entry, &tbl, &e, &nxt);
    // Key on the adapter sig alone; rt is in the bucket (see jl_lookup_abi_adapter).
    jl_value_t *key = entry->sigt; // rooted via `entry`
    jl_typemap_entry_t *te = jl_typemap_list_entry(&jl_abi_adapters->cache, key);
    if (te == NULL) {
        jl_typemap_list_insert(&jl_abi_adapters->cache, (jl_value_t*)jl_abi_adapters, key,
                (jl_value_t*)entry, offsetof(jl_abi_adapter_t, next));
        JL_GC_POP();
        return;
    }
    jl_value_t *repr = jl_atomic_load_relaxed((_Atomic(jl_value_t*)*)&te->func.value);
    if (jl_is_genericmemory(repr)) {
        // tier 3: prepend into the ci-bucket; publish a grown table if it reallocated.
        tbl = abi_adapter_eqtable_prepend((jl_genericmemory_t*)repr, entry);
        if ((jl_value_t*)tbl != repr) {
            jl_atomic_store_release((_Atomic(jl_value_t*)*)&te->func.value, (jl_value_t*)tbl);
            jl_gc_wb(te, tbl);
        }
        JL_GC_POP();
        return;
    }
    // tiers 1-2: a record list. Count it to decide between appending and promoting.
    jl_abi_adapter_t *head = (jl_abi_adapter_t*)repr;
    size_t count = 1;
    for (jl_abi_adapter_t *n = head; (n = jl_atomic_load_relaxed(&n->next)) != NULL; )
        count++;
    if (count < MAX_ADAPTER_LIST_COUNT) {
        jl_typemap_list_append((jl_value_t*)head, (jl_value_t*)entry,
                offsetof(jl_abi_adapter_t, next));
        JL_GC_POP();
        return;
    }
    // tier 2 -> 3: promote the chain to a ci-keyed eqtable, then publish it. Regrouping
    // relinks `.next` (concurrent old-chain readers may miss -> locked recheck recovers).
    tbl = jl_alloc_memory_any(16);
    e = head;
    while (e != NULL) {
        nxt = jl_atomic_load_relaxed(&e->next);
        tbl = abi_adapter_eqtable_prepend(tbl, e);
        e = nxt;
    }
    tbl = abi_adapter_eqtable_prepend(tbl, entry);
    jl_atomic_store_release((_Atomic(jl_value_t*)*)&te->func.value, (jl_value_t*)tbl);
    jl_gc_wb(te, tbl);
    JL_GC_POP();
}

// Allocate an ABI-adapter cache record. Caller keeps the key fields (`sigt`/`rt`/`ci`)
// rooted. `next` starts as the chain tail.
JL_DLLEXPORT jl_abi_adapter_t *jl_new_abi_adapter(jl_value_t *sigt, jl_value_t *rt,
        jl_code_instance_t *ci, int specsig, jl_abi_kind_t kind, size_t nargs, void *fptr) JL_CANSAFEPOINT
{
    jl_task_t *ct = jl_current_task;
    jl_abi_adapter_t *e = (jl_abi_adapter_t*)jl_gc_alloc(ct->ptls, sizeof(jl_abi_adapter_t), jl_abi_adapter_type);
    e->sigt = sigt;
    e->rt = rt;
    e->specsig = specsig ? 1 : 0;
    e->kind = (size_t)kind;
    e->nargs = nargs;
    e->ci = ci;
    e->fptr = fptr;
    jl_atomic_store_relaxed(&e->next, (jl_abi_adapter_t*)NULL);
    return e;
}

// Insert `e` into the running cache if its key is absent and return the canonical record;
// keep-first, like jl_specializations_get_or_insert (a losing `e` is left standalone). The
// JIT path inserts freshly-built records here (under its already-held writelock; the lock is
// reentrant), and the load fixup re-inserts image-restored records, whose `fptr` must already
// be wired (jl_update_all_fptrs).
JL_DLLEXPORT jl_abi_adapter_t *jl_insert_abi_adapter(jl_abi_adapter_t *e) JL_CANSAFEPOINT
{
    jl_abi_adapter_t *canonical = NULL;
    JL_GC_PUSH2(&e, &canonical);
    JL_LOCK(&jl_abi_adapters->writelock);
    canonical = jl_lookup_abi_adapter(e->sigt, e->rt, e->ci, e->specsig, (jl_abi_kind_t)e->kind, e->nargs);
    if (canonical == NULL) {
        abi_adapter_insert(e);
        canonical = e;
    }
    JL_UNLOCK(&jl_abi_adapters->writelock);
    JL_GC_POP();
    return canonical;
}
