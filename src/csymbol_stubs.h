// This file is a part of Julia. License is MIT: https://julialang.org/license

#ifndef JL_CSYMBOL_STUBS_H
#define JL_CSYMBOL_STUBS_H

#include <memory>
#include <mutex>

// IMPORTANT: LLVM headers must be parsed before any julia.h pollution.
// julia.h pulls in libuv → termios, which defines macros like `CR1` that
// collide with LLVM template parameters (ConstantRange.h has a parameter
// named CR1). The trick: include the JITLink-specific LLVM headers we
// need FIRST, then include jitlayers.h (which itself orders its LLVM
// includes before julia.h).
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/ExecutionEngine/JITLink/JITLink.h>
#include <llvm/ExecutionEngine/JITLink/aarch64.h>
#include <llvm/ExecutionEngine/JITLink/riscv.h>
#include <llvm/ExecutionEngine/JITLink/x86_64.h>
#include <llvm/ExecutionEngine/Orc/Core.h>
#include <llvm/ExecutionEngine/Orc/ObjectLinkingLayer.h>
#include <llvm/Support/Error.h>

// jitlayers.h must precede ccall_data.h to avoid macro pollution: jitlayers.h
// orders its own LLVM includes before julia.h, which avoids parsing LLVM
// templates after libuv → termios pollutes names like CR1.
#include "jitlayers.h"  // jl_ccall_spec_t + DenseMapInfo specialization (also pulls in julia.h)
#include "ccall_data.h"

namespace julia {
namespace csymbol {

// csymbol_data_t is defined in ccall_data.h (shared with the runtime side
// and the cglobal lazy-lookup path).

// Emit a small reentry trampoline (16 bytes per arch) that pushes &data
// onto the stack and tail-branches to the shared resolver:
//
//   x86-64:  push $0; lea data(%rip), %r11; push %r11; jmp ccall_reentry_trampoline
//   AArch64: adrp x16, data; add x16, x16, :lo12:data;
//            str x16, [sp, #-16]!; b ccall_reentry_trampoline
//
// Pushing &data (rather than leaving it in a scratch register) makes the
// resolver robust against the system PLT's lazy-resolve path clobbering
// scratch regs when binding ccall_reentry_trampoline itself on the first
// call. The asm resolver reads &data back from the stack.
llvm::jitlink::Block &emitCCallTrampoline(llvm::jitlink::LinkGraph &G,
                                          llvm::jitlink::Section &Sec,
                                          llvm::jitlink::Symbol &DataSym,
                                          llvm::jitlink::Symbol &ResolverSym);

// Manager for cross-graph-shared resources backing ccall and cglobal sites.
//
// Each unique jl_ccall_spec_t maps to one MaterializationUnit that, on first
// lookup, builds a per-spec (stub, ptr-slot, trampoline, data) quartet plus
// auxiliary string globals. Multiple caller graphs that reference the same
// spec — whether as a ccall (calling into the stub) or a cglobal (loading
// from the slot) — all resolve through the JITDylib to the same MU and
// therefore the same materialized resources.
//
// Two consumer entry points expose the per-spec resources by canonical
// SymbolStringPtr:
//
//   - getOrCreateStub(spec) → stub function symbol. Used by ccall callers
//     whose graph contains a call to the stub. First call:
//       stub: jmp *(ptr_slot) → tramp → push &data → ccall_reentry_trampoline
//       → resolver patches *ptr_slot to the resolved target.
//     Subsequent calls: stub: jmp *(ptr_slot) → resolved target.
//
//   - getOrCreateSlot(spec) → ptr-slot data symbol. Used by cglobal callers
//     whose graph contains an inline load/store of the cache slot
//     (emit_csymbol_lazy_lookup's diamond). The slot value flips from
//     &tramp to the resolved address on the first miss; cglobal's diamond
//     stores the address directly into the slot via the visible IR-level
//     store, mirroring what the trampoline does for ccall.
//
// Either entry point materializes the full quartet on first request — the
// resources are small (one PLT-style stub, one data struct, one trampoline),
// JITLink dead-symbol elimination drops anything no caller references in a
// given session, and we avoid the complexity of upgrading a slot-only spec
// to a slot+stub spec when a later ccall consumer arrives.
class CSymbolStubManager {
public:
    static llvm::Expected<std::unique_ptr<CSymbolStubManager>>
    Create(llvm::orc::ObjectLinkingLayer &OLL, llvm::orc::JITDylib &JD);

    // Stub symbol for ccall consumers. First call for a given spec
    // registers the per-spec MaterializationUnit; subsequent calls return
    // the cached SymbolStringPtr.
    llvm::orc::SymbolStringPtr getOrCreateStub(const jl_ccall_spec_t &spec);

    // Slot symbol for cglobal consumers. Same per-spec MU as the stub
    // path; this just returns the slot's canonical name from the cached
    // entry. Idempotent.
    llvm::orc::SymbolStringPtr getOrCreateSlot(const jl_ccall_spec_t &spec);

    CSymbolStubManager(llvm::orc::ObjectLinkingLayer &OLL,
                       llvm::orc::JITDylib &JD,
                       llvm::orc::ResourceTrackerSP RT,
                       llvm::orc::SymbolStringPtr ResolverName);

private:
    // Per-spec entry: holds the canonical names of every exported symbol
    // the MU defines, so getOrCreate{Stub,Slot} can hand them out without
    // re-materializing.
    struct Entry {
        llvm::orc::SymbolStringPtr StubName;
        llvm::orc::SymbolStringPtr SlotName;
    };

    class StubMU;
    friend class StubMU;

    // First-time setup: assign canonical names + register the MU. Called
    // under Mtx. Returns a reference to the per-spec Entry.
    Entry &getOrCreateLocked(const jl_ccall_spec_t &spec, bool &Registered);

    void emitGraph(std::unique_ptr<llvm::orc::MaterializationResponsibility> MR,
                   const Entry &E,
                   const jl_ccall_spec_t &Spec);

    llvm::orc::JITDylib &JD;
    llvm::orc::ExecutionSession &ES;
    llvm::orc::ObjectLinkingLayer &OLL;
    llvm::orc::ResourceTrackerSP RT;
    llvm::orc::SymbolStringPtr ResolverName;

    std::mutex Mtx;
    llvm::DenseMap<jl_ccall_spec_t, Entry> SpecEntries;
    size_t NextId = 0;
};

} // namespace csymbol
} // namespace julia

#endif // JL_CSYMBOL_STUBS_H
