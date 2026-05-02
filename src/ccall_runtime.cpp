// This file is a part of Julia. License is MIT: https://julialang.org/license

// Runtime side of the lazy csymbol-resolution mechanism. Two related
// entry points:
//
//   - csymbol_lookup(data)
//       The pure dlsym path: takes a csymbol_data_t and returns the
//       resolved address. Does NOT touch data->ptr_slot. Used by inline
//       cglobal lookups, where the codegen emits the cache-store as a
//       visible IR instruction so LLVM can reason about init-once
//       semantics (LICM the load + cold call out of loops).
//
//   - ccall_resolve_and_patch(data)
//       Wraps csymbol_lookup with an atomic release store into
//       *data->ptr_slot. Used by the lazy-ccall asm trampoline
//       (ccall_reenter.S), which doesn't have a convenient place to
//       emit the store from asm — the C wrapper does it.
//
// Lives in libjulia-internal (not libjulia-codegen) because pkgimages
// link against libjulia-internal at runtime; the codegen-side machinery
// (CSymbolStubManager, aot_emit_ccall_stubs, emit_csymbol_lazy_lookup) is
// in libjulia-codegen.

#include "ccall_data.h"
#include "julia_internal.h"
#include "support/htable.h"

#include <atomic>

// --- resolved-slot registry (dlclose invalidation) ---
//
// Every cache slot the resolver populates is recorded here alongside the
// value that must be restored to send the next access back through the
// cold path:
//
//   - ccall stub slots start out pointing at the trampoline, so the reset
//     value is that trampoline address.
//   - cglobal slots start out NULL (codegen branches on `slot == NULL`),
//     so the reset value is NULL.
//
// `jl_dlclose` walks the registry and restores every entry. Because a
// slot is shared by all sites with the same (lib, sym) spec, a stale
// entry would otherwise be reused by an unrelated call site after the
// owning library was unloaded — jumping into an unmapped page.
//
// Invalidating on *any* dlclose over-approximates (we do not track which
// library a given symbol resolved through), but dlclose is rare and the
// only cost is one extra resolution per live symbol afterwards.
static htable_t csymbol_resolved_slots;
static jl_mutex_t csymbol_resolved_slots_lock;
static int csymbol_resolved_slots_initialized = 0;

// Record `slot`'s unresolved value. First registration wins: a racing
// second resolver may observe the slot *after* the winner's patch, and
// must not overwrite the correct reset value with the resolved pointer.
// This is safe because each resolver registers before it stores, so any
// thread that can see a patched slot can also see the winner's entry.
static void csymbol_register_slot(void **slot, void *reset) JL_NOTSAFEPOINT
{
    if (slot == NULL)
        return;
    JL_LOCK_NOGC(&csymbol_resolved_slots_lock);
    if (!csymbol_resolved_slots_initialized) {
        htable_new(&csymbol_resolved_slots, 32);
        csymbol_resolved_slots_initialized = 1;
    }
    if (ptrhash_get(&csymbol_resolved_slots, (void *)slot) == HT_NOTFOUND)
        ptrhash_put(&csymbol_resolved_slots, (void *)slot, reset);
    JL_UNLOCK_NOGC(&csymbol_resolved_slots_lock);
}

extern "C" JL_DLLEXPORT
void jl_csymbol_invalidate_cache(void) JL_NOTSAFEPOINT
{
    JL_LOCK_NOGC(&csymbol_resolved_slots_lock);
    if (csymbol_resolved_slots_initialized) {
        for (size_t i = 0; i < csymbol_resolved_slots.size; i += 2) {
            void *reset = csymbol_resolved_slots.table[i + 1];
            if (reset == HT_NOTFOUND)
                continue;
            void **slot = (void **)csymbol_resolved_slots.table[i];
            // Release store, mirroring ccall_resolve_and_patch: a thread
            // that observes the reset value re-enters the cold path.
            std::atomic_store_explicit(
                reinterpret_cast<std::atomic<void *> *>(slot),
                reset, std::memory_order_release);
        }
        htable_reset(&csymbol_resolved_slots, 32);
    }
    JL_UNLOCK_NOGC(&csymbol_resolved_slots_lock);
}

// If `v` is a global reference (a GlobalRef, or the binding partition that
// optimized IR resolves one to), evaluate it; otherwise return as-is.
static jl_value_t *eval_if_globalref(jl_value_t *v) JL_CANSAFEPOINT
{
    if (jl_is_globalref(v)) {
        size_t world = jl_atomic_load_acquire(&jl_world_counter);
        v = jl_eval_globalref((jl_globalref_t*)v, world);
    }
    else if (jl_is_binding_partition(v)) {
        jl_binding_partition_t *bpart = (jl_binding_partition_t*)v;
        v = jl_get_binding_partition_leaf_value(bpart);
        if (v == NULL) {
            jl_binding_t *bnd = jl_binding_partition_owner(bpart);
            jl_undefined_var_error(bnd->globalref->name, (jl_value_t*)bnd->globalref->mod);
        }
    }
    return v;
}

// Resolve a tuple element to a C string (function name). The element is a
// global reference (evaluated at first-call time), Symbol, or String. Throws
// on any other type.
static const char *resolve_func_value(jl_value_t *v) JL_CANSAFEPOINT
{
    v = eval_if_globalref(v);
    if (jl_is_symbol(v))
        return jl_symbol_name((jl_sym_t*)v);
    if (jl_is_string(v))
        return jl_string_data(v);
    jl_type_error("ccall function name", (jl_value_t*)jl_symbol_type, v);
}

// Pure resolution, no registry side effects. Both entry points below wrap
// this with the registration appropriate to their slot's unresolved value.
static void *csymbol_lookup_impl(const struct csymbol_data_t *data) JL_CANSAFEPOINT
{
    // Static caches first. If both are populated, codegen knew the
    // (lib, func) pair statically and we can skip touching `target`.
    const char *func = data->func;
    const char *lib = data->lib;

    // Cached lib value (only populated when we need to call
    // jl_lazy_load_and_lookup — i.e. the lib slot is dynamic and not a
    // simple sentinel/string). Stays NULL for the static-lib path.
    //
    // GC rooting: `lib_dyn` is the result of evaluating a global reference
    // (potentially a LazyLibrary or other heap value), and the path that
    // consumes it (jl_lazy_load_and_lookup → jl_apply_generic) can
    // allocate / safepoint inside dispatch. Push it onto the GC frame
    // before any of those callsites can run.
    jl_value_t *lib_dyn = nullptr;
    JL_GC_PUSH1(&lib_dyn);

    if ((func == nullptr || lib == nullptr) && data->target != nullptr) {
        // The `target` field is a *slot* pointer — one level of indirection
        // beyond the value itself. literal_pointer_val_slot (in cgutils.cpp)
        // emits a GV whose address is what gets stored into the data struct;
        // the GV's contents are fixed up to the actual jl_value_t* at link
        // time and across pkgimage relocation. Load through the slot here
        // to recover the svec.
        jl_svec_t *target = *(jl_svec_t**)data->target;
        size_t n = jl_svec_len(target);
        if (func == nullptr)
            func = resolve_func_value(jl_svecref(target, 0));
        if (lib == nullptr && n >= 2) {
            lib_dyn = eval_if_globalref(jl_svecref(target, 1));
        }
    }

    void *out;
    if (lib != nullptr) {
        // Bypass jl_load_and_lookup (it requires a per-call hnd_cache slot
        // that we don't allocate). jl_get_library_ has its own libMap cache,
        // so the dlopen cost is amortized over the process.
        void *handle = jl_get_library_(lib, /*throw_err=*/1);
        if (!jl_dlsym(handle, func, &out, /*throw_err=*/1, /*verbose=*/1))
            out = nullptr;
    } else if (lib_dyn != nullptr) {
        // Dynamic ref: lib_dyn may be a String, Symbol, or LazyLibrary
        // value. jl_lazy_load_and_lookup handles all three.
        jl_value_t *fn_sym = (jl_value_t*)jl_symbol(func);
        out = jl_lazy_load_and_lookup(lib_dyn, fn_sym);
    } else {
        // No lib hint — RTLD_DEFAULT lookup.
        void *handle = jl_get_library_(nullptr, /*throw_err=*/1);
        if (!jl_dlsym(handle, func, &out, /*throw_err=*/1, /*verbose=*/1))
            out = nullptr;
    }
    JL_GC_POP();
    return out;
}

// The resolution runs Julia code (it evaluates globals, calls `dlopen` through
// dispatch, and throws on failure), but a `gc_safe` ccall reaches the resolver
// with the thread in the GC-safe state, so make it GC-unsafe for the duration.
// If the resolution throws, the exception handler restores the GC state that
// was saved when it was entered.
static void *csymbol_lookup_unsafe(const struct csymbol_data_t *data) JL_CANSAFEPOINT_ENTER_LEAVE
{
    jl_task_t *ct = jl_current_task;
    int8_t gc_state = jl_gc_unsafe_enter(ct->ptls);
    void *out = csymbol_lookup_impl(data);
    jl_gc_unsafe_leave(ct->ptls, gc_state);
    return out;
}

extern "C" JL_DLLEXPORT
void *csymbol_lookup(const struct csymbol_data_t *data) JL_CANSAFEPOINT_ENTER_LEAVE
{
    void *out = csymbol_lookup_unsafe(data);
    // cglobal path: codegen emits the cache store itself and branches on
    // `slot == NULL`, so NULL is the value that re-arms the cold path.
    csymbol_register_slot(data->ptr_slot, NULL);
    return out;
}

extern "C" JL_DLLEXPORT
void *ccall_resolve_and_patch(const struct csymbol_data_t *data) JL_CANSAFEPOINT_ENTER_LEAVE
{
    void *target = csymbol_lookup_unsafe(data);
    void **slot = data->ptr_slot;
    // Register *before* patching: the slot still holds the trampoline
    // address, which is what re-arms the cold path. See the first-wins
    // note on csymbol_register_slot for why the ordering matters. The read
    // is atomic because a racing resolver may be patching this same slot.
    void *unresolved = std::atomic_load_explicit(
        reinterpret_cast<std::atomic<void *> *>(slot), std::memory_order_acquire);
    csymbol_register_slot(slot, unresolved);
    // Atomic release store so other threads observing *ptr_slot see the new
    // value with proper ordering relative to dlsym's side effects.
    std::atomic_store_explicit(
        reinterpret_cast<std::atomic<void *> *>(slot),
        target, std::memory_order_release);
    return target;
}
