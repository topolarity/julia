// This file is a part of Julia. License is MIT: https://julialang.org/license

// Layout of the per-csymbol data struct, shared between codegen
// (CSymbolStubManager / aot_emit_ccall_stubs / lazy cglobal lookup) and the
// runtime resolver (ccall_resolve_and_patch). Kept in its own header so
// the runtime side (compiled into libjulia-internal) doesn't need to drag
// in the codegen-side LLVM headers.
//
// One csymbol_data_t instance per unique (lib, sym) reference in codegen.
// `ptr_slot` holds the cached resolved address; the resolver atomically
// stores into it on the cold path so subsequent accesses see the cached
// pointer with no further dlopen+dlsym work.
//
// Shape is identical for ccall and cglobal — both want "where do I find
// this symbol, and where do I cache the answer."

#ifndef JL_CSYMBOL_DATA_H
#define JL_CSYMBOL_DATA_H

#include "julia.h"

#ifdef __cplusplus
extern "C" {
#endif

struct csymbol_data_t {
    void **ptr_slot;                   // back-ref: where the resolver writes target
    const char *lib;                   // static cache for library (NULL when dynamic)
    const char *func;                  // static cache for function name (NULL when dynamic)
    // Target spec as a Core.svec of 1 or 2 elements: (fn,) or (fn, lib).
    // Populated when at least one of `lib`/`func` is NULL. Each element is
    // either pre-evaluated (Symbol, String, LazyLibrary, ...) or a
    // GlobalRef the resolver evaluates at first-call time. NULL when the
    // (lib, func) pair is fully resolvable from the static caches above.
    jl_value_t *target;
};

// Pure dlsym lookup — does NOT touch data->ptr_slot. Used by inline
// cglobal codegen so the codegen can emit the cache-store visibly,
// letting LLVM reason about init-once semantics.
void *csymbol_lookup(const struct csymbol_data_t *data);

// Wraps csymbol_lookup with an atomic release store into *data->ptr_slot.
// Used by the lazy-ccall asm trampoline (which doesn't easily emit the
// store from asm — the C wrapper does it).
void *ccall_resolve_and_patch(const struct csymbol_data_t *data);

#ifdef __cplusplus
} // extern "C"
#endif

#endif // JL_CSYMBOL_DATA_H
