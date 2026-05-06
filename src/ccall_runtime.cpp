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

#include <atomic>

// If `v` is a GlobalRef, evaluate it; otherwise return as-is.
static jl_value_t *eval_if_globalref(jl_value_t *v)
{
    if (jl_is_globalref(v)) {
        size_t world = jl_atomic_load_acquire(&jl_world_counter);
        v = jl_eval_globalref((jl_globalref_t*)v, world);
    }
    return v;
}

// Resolve a tuple element to a C string (function name). The element is a
// GlobalRef (eval'd at first-call time), Symbol, or String. Throws on any
// other type.
static const char *resolve_func_value(jl_value_t *v)
{
    v = eval_if_globalref(v);
    if (jl_is_symbol(v))
        return jl_symbol_name((jl_sym_t*)v);
    if (jl_is_string(v))
        return jl_string_data(v);
    jl_type_error("ccall function name", (jl_value_t*)jl_symbol_type, v);
}

extern "C" JL_DLLEXPORT
void *csymbol_lookup(const struct csymbol_data_t *data)
{
    // Static caches first. If both are populated, codegen knew the
    // (lib, func) pair statically and we can skip touching `target`.
    const char *func = data->func;
    const char *lib = data->lib;

    // Cached lib value (only populated when we need to call
    // jl_lazy_load_and_lookup — i.e. the lib slot is dynamic and not a
    // simple sentinel/string). Stays NULL for the static-lib path.
    //
    // GC rooting: `lib_dyn` is the result of evaluating a GlobalRef
    // (potentially a LazyLibrary or other heap value), and the path that
    // consumes it (jl_lazy_load_and_lookup → jl_apply_generic) can
    // allocate / safepoint inside dispatch. Push it onto the GC frame
    // before any of those callsites can run. The actual_id / actual_name
    // slots are used only on the AbstractSystemLibrary verification path
    // (n == 4); they hold the results of dlid()/dlname() across the second
    // jl_apply_generic call.
    jl_value_t *lib_dyn = nullptr;
    jl_value_t *actual_id = nullptr;
    jl_value_t *actual_name = nullptr;
    JL_GC_PUSH3(&lib_dyn, &actual_id, &actual_name);

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
        if (n == 4) {
            // AbstractSystemLibrary form: `target` is (fn, lib_ref, lib_id, lib_name).
            // Subtypes of AbstractSystemLibrary opt into a stable-identity
            // contract — dlid() and dlname() must be invariant for the life
            // of the handle. Enforce that here, before we dlopen, by comparing
            // the values frozen at definition time against what the lib_obj
            // returns now. Mismatch indicates a buggy subtype implementation
            // (or a LazyLibrary whose path was mutated).
            if (jl_libdl_dlid_func == nullptr || jl_libdl_dlname_func == nullptr)
                jl_error("AbstractSystemLibrary identity check requires Libdl to be loaded");
            jl_value_t *expected_id = jl_svecref(target, 2);
            jl_value_t *expected_name = jl_svecref(target, 3);
            actual_id = jl_apply_generic(jl_libdl_dlid_func, &lib_dyn, 1);
            actual_name = jl_apply_generic(jl_libdl_dlname_func, &lib_dyn, 1);
            if (!jl_egal(actual_id, expected_id) || !jl_egal(actual_name, expected_name))
                jl_errorf("ccall: AbstractSystemLibrary identity changed since definition "
                          "(dlid()/dlname() must be stable for AbstractSystemLibrary subtypes)");
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

extern "C" JL_DLLEXPORT
void *ccall_resolve_and_patch(const struct csymbol_data_t *data)
{
    void *target = csymbol_lookup(data);
    // Atomic release store so other threads observing *ptr_slot see the new
    // value with proper ordering relative to dlsym's side effects.
    std::atomic_store_explicit(
        reinterpret_cast<std::atomic<void *> *>(data->ptr_slot),
        target, std::memory_order_release);
    return target;
}
