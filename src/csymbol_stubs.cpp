// This file is a part of Julia. License is MIT: https://julialang.org/license

#include "csymbol_stubs.h"

#include <atomic>
#include <cstring>

#include "julia_internal.h"

using namespace llvm;
using namespace llvm::orc;
using namespace llvm::jitlink;

namespace julia {
namespace csymbol {

// ---------------------------------------------------------------------------
// Per-arch edge-kind helpers.
// ---------------------------------------------------------------------------

#if defined(_CPU_X86_64_) || defined(__x86_64__)
static constexpr Edge::Kind getPointer64Kind() { return jitlink::x86_64::Pointer64; }
#elif defined(_CPU_AARCH64_) || defined(__aarch64__)
static constexpr Edge::Kind getPointer64Kind() { return jitlink::aarch64::Pointer64; }
#elif defined(_CPU_RISCV64_) || (defined(__riscv) && __riscv_xlen == 64)
static constexpr Edge::Kind getPointer64Kind() { return jitlink::riscv::R_RISCV_64; }
#else
static constexpr Edge::Kind getPointer64Kind() { return Edge::FirstRelocation; }
#endif

// ---------------------------------------------------------------------------
// Per-arch trampoline emitter.
//
// We emit a small trampoline (27 bytes on x86-64, 16 on AArch64, 40 on
// RISC-V) that pushes &data onto the stack and tail-branches to
// ccall_reentry_trampoline. The edges follow the code model the JIT uses on
// each architecture: absolute 64-bit addresses on x86-64 and RISC-V (large),
// adrp-based PC-relative ones on AArch64 (small).
// ---------------------------------------------------------------------------

#if defined(_CPU_X86_64_) || defined(__x86_64__)
namespace {
// We push &data onto the stack BEFORE branching to the shared resolver.
// This is robust against the system PLT's lazy-resolve clobbering scratch
// registers (%r10/%r11 on x86-64): once the value is on the stack it
// survives any PLT bookkeeping. The asm resolver reads it from the stack.
//
// We push *two* slots (16 bytes total) so that the resolver is entered with
// %rsp = 8 mod 16 — i.e. the standard SysV "right after a `call`" alignment.
// That matches what the dynamic linker's lazy-resolution path
// (_dl_runtime_resolve) expects when it's invoked to bind the resolver
// itself on the first call. Without the extra push, %rsp would be 0 mod 16
// at resolver entry, which works on glibc by accident but is not portable.
//
//   push   $0                  (2 bytes; 6a 00)        ; alignment padding
//   movabs $data, %r11         (10 bytes; imm64 at offset 4)
//   push   %r11                (2 bytes; 41 53)        ; &data
//   movabs $resolver, %r11     (10 bytes; imm64 at offset 16)
//   jmp    *%r11               (3 bytes; 41 ff e3)
//
// The JIT uses the large code model on x86-64, so the sections of this graph
// (and libjulia, where the resolver lives) may be more than 2GB apart; both
// references are therefore absolute 64-bit addresses, not rel32.
constexpr char TrampolineBytes_x86_64[27] = {
    static_cast<char>(0x6a), 0x00,                       // push $0 (alignment)
    0x49, static_cast<char>(0xbb),                       // movabs $data, %r11
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x41, 0x53,                                          // push %r11
    0x49, static_cast<char>(0xbb),                       // movabs $resolver, %r11
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x41, static_cast<char>(0xff), static_cast<char>(0xe3), // jmp *%r11
};
} // namespace

Block &emitCCallTrampoline(LinkGraph &G, Section &Sec,
                           Symbol &DataSym, Symbol &ResolverSym) {
    auto Content = ArrayRef<char>(TrampolineBytes_x86_64,
                                  sizeof(TrampolineBytes_x86_64));
    auto &B = G.createContentBlock(Sec, Content,
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/1, /*AlignmentOffset=*/0);
    B.addEdge(x86_64::Pointer64, /*Offset=*/4,  DataSym,     /*Addend=*/0);
    B.addEdge(x86_64::Pointer64, /*Offset=*/16, ResolverSym, /*Addend=*/0);
    return B;
}

#elif defined(_CPU_AARCH64_) || defined(__aarch64__)
namespace {
// We push &data onto the stack BEFORE branching to the shared resolver.
// This is robust against the system PLT's lazy-resolve clobbering scratch
// registers (x16/x17 on AArch64): once the value is on the stack it
// survives any PLT bookkeeping. The asm resolver reads it from the stack.
//
// adrp x16, page                (4 bytes; offset 0; Page21 reloc)
// add  x16, x16, :lo12:offset   (4 bytes; offset 4; PageOffset12 reloc)
// str  x16, [sp, #-16]!         (4 bytes; offset 8; pre-indexed push)
// b    rel26                    (4 bytes; offset 12; Branch26PCRel reloc)
constexpr char TrampolineBytes_aarch64[16] = {
    0x10, 0x00, 0x00, static_cast<char>(0x90),  // adrp x16, page
    0x10, 0x02, 0x00, static_cast<char>(0x91),  // add  x16, x16, :lo12:
    static_cast<char>(0xf0), 0x0f, 0x1f, static_cast<char>(0xf8), // str x16, [sp, #-16]!
    0x00, 0x00, 0x00, 0x14,                     // b .
};
} // namespace

Block &emitCCallTrampoline(LinkGraph &G, Section &Sec,
                           Symbol &DataSym, Symbol &ResolverSym) {
    auto Content = ArrayRef<char>(TrampolineBytes_aarch64,
                                  sizeof(TrampolineBytes_aarch64));
    auto &B = G.createContentBlock(Sec, Content,
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/4, /*AlignmentOffset=*/0);
    B.addEdge(aarch64::Page21,        /*Offset=*/0,  DataSym,     /*Addend=*/0);
    B.addEdge(aarch64::PageOffset12,  /*Offset=*/4,  DataSym,     /*Addend=*/0);
    B.addEdge(aarch64::Branch26PCRel, /*Offset=*/12, ResolverSym, /*Addend=*/0);
    return B;
}

#elif defined(_CPU_RISCV64_) || (defined(__riscv) && __riscv_xlen == 64)
namespace {
// We push &data onto the stack BEFORE branching to the shared resolver.
// This is robust against the system PLT's lazy-resolve clobbering scratch
// registers (t-regs on RISC-V): once the value is on the stack it survives
// any PLT bookkeeping. The asm resolver reads it from the stack.
//
//   auipc t0, 0                      (4 bytes; offset 0)
//   ld    t1, 32(t0)                 (4 bytes; offset 4)  ; resolver
//   ld    t0, 24(t0)                 (4 bytes; offset 8)  ; &data
//   addi  sp, sp, -16                (4 bytes; offset 12)
//   sd    t0, 0(sp)                  (4 bytes; offset 16)
//   jr    t1                         (4 bytes; offset 20)
//   .dword data                      (8 bytes; offset 24; R_RISCV_64)
//   .dword resolver                  (8 bytes; offset 32; R_RISCV_64)
//
// The JIT uses the large code model on RISC-V, so the sections of this graph
// (and libjulia, where the resolver lives) may be out of auipc range of each
// other. As in the large code model, the addresses are instead loaded from
// literals placed in the trampoline itself.
constexpr char TrampolineBytes_riscv64[40] = {
    static_cast<char>(0x97), 0x02, 0x00, 0x00,                         // auipc t0, 0
    0x03, static_cast<char>(0xb3), 0x02, 0x02,                         // ld    t1, 32(t0)
    static_cast<char>(0x83), static_cast<char>(0xb2), static_cast<char>(0x82), 0x01, // ld t0, 24(t0)
    0x13, 0x01, 0x01, static_cast<char>(0xff),                         // addi  sp, sp, -16
    0x23, 0x30, 0x51, 0x00,                                            // sd    t0, 0(sp)
    0x67, 0x00, 0x03, 0x00,                                            // jr    t1
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,                    // .dword data
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,                    // .dword resolver
};
} // namespace

Block &emitCCallTrampoline(LinkGraph &G, Section &Sec,
                           Symbol &DataSym, Symbol &ResolverSym) {
    auto Content = ArrayRef<char>(TrampolineBytes_riscv64,
                                  sizeof(TrampolineBytes_riscv64));
    auto &B = G.createContentBlock(Sec, Content,
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/8, /*AlignmentOffset=*/0);
    B.addEdge(riscv::R_RISCV_64, /*Offset=*/24, DataSym,     /*Addend=*/0);
    B.addEdge(riscv::R_RISCV_64, /*Offset=*/32, ResolverSym, /*Addend=*/0);
    return B;
}

#else
Block &emitCCallTrampoline(LinkGraph &G, Section &Sec,
                           Symbol &DataSym, Symbol &ResolverSym) {
    report_fatal_error("CCall lazy stubs not yet implemented for this arch");
}
#endif

// ---------------------------------------------------------------------------
// Per-arch ptr-slot and stub creators.
//
// The ptr slot comes from JITLink's getAnonymousPointerCreator, and on AArch64
// so does the stub (getPointerJumpStubCreator); its adrp reach matches the
// small code model the JIT uses there. Upstream JITLink does NOT (yet) provide
// those helpers for RISC-V, so we hand-roll equivalent block layouts.
// ---------------------------------------------------------------------------

#if defined(_CPU_RISCV64_) || (defined(__riscv) && __riscv_xlen == 64)
namespace {
// 8 bytes of zero-initialized backing storage, fixed up at link time by an
// R_RISCV_64 edge to the trampoline.
constexpr char PtrSlotNullBytes[8] = {};

// 24-byte indirect-jump stub: load *ptr into t0 and jr to it. The address of
// the ptr slot is loaded from a literal in the stub (see the trampoline above).
//
//   auipc t0, 0                     (4 bytes; offset 0)
//   ld    t0, 16(t0)                (4 bytes; offset 4)  ; &ptr
//   ld    t0, 0(t0)                 (4 bytes; offset 8)  ; ptr
//   jr    t0                        (4 bytes; offset 12)
//   .dword ptr                      (8 bytes; offset 16; R_RISCV_64)
constexpr char StubBytes_riscv64[24] = {
    static_cast<char>(0x97), 0x02, 0x00, 0x00,                         // auipc t0, 0
    static_cast<char>(0x83), static_cast<char>(0xb2), 0x02, 0x01,      // ld    t0, 16(t0)
    static_cast<char>(0x83), static_cast<char>(0xb2), 0x02, 0x00,      // ld    t0, 0(t0)
    0x67, static_cast<char>(0x80), 0x02, 0x00,                         // jr    t0
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,                    // .dword ptr
};
} // namespace

static Symbol &createCCallPtrSlot(LinkGraph &G, Section &Sec, Symbol &TrampSym) {
    auto &B = G.createContentBlock(Sec, ArrayRef<char>(PtrSlotNullBytes, 8),
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/8, /*AlignmentOffset=*/0);
    B.addEdge(riscv::R_RISCV_64, /*Offset=*/0, TrampSym, /*Addend=*/0);
    return G.addAnonymousSymbol(B, /*Offset=*/0, /*Size=*/8,
                                /*IsCallable=*/false, /*IsLive=*/false);
}

static Symbol &createCCallStub(LinkGraph &G, Section &Sec, Symbol &PtrSym) {
    auto Content = ArrayRef<char>(StubBytes_riscv64, sizeof(StubBytes_riscv64));
    auto &B = G.createContentBlock(Sec, Content,
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/8, /*AlignmentOffset=*/0);
    B.addEdge(riscv::R_RISCV_64, /*Offset=*/16, PtrSym, /*Addend=*/0);
    return G.addAnonymousSymbol(B, /*Offset=*/0,
                                /*Size=*/sizeof(StubBytes_riscv64),
                                /*IsCallable=*/true, /*IsLive=*/false);
}

#else // x86-64, AArch64, etc.

static Symbol &createCCallPtrSlot(LinkGraph &G, Section &Sec, Symbol &TrampSym) {
    return jitlink::getAnonymousPointerCreator(G.getTargetTriple())(
        G, Sec, &TrampSym, /*InitialAddend=*/0);
}

#if defined(_CPU_X86_64_) || defined(__x86_64__)
namespace {
// 13-byte indirect-jump stub. JITLink's own pointer jump stub reaches the
// pointer with a rel32, which assumes the whole graph is allocated as one
// contiguous slab. The JIT memory manager allocates each protection class
// separately, so (as for all JIT code on x86-64) use the large code model:
//
//   movabs $ptr, %r11         (10 bytes; imm64 at offset 2)
//   jmp    *(%r11)            (3 bytes; 41 ff 23)
constexpr char StubBytes_x86_64[13] = {
    0x49, static_cast<char>(0xbb),                       // movabs $ptr, %r11
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x41, static_cast<char>(0xff), 0x23,                 // jmp *(%r11)
};
} // namespace

static Symbol &createCCallStub(LinkGraph &G, Section &Sec, Symbol &PtrSym) {
    auto Content = ArrayRef<char>(StubBytes_x86_64, sizeof(StubBytes_x86_64));
    auto &B = G.createContentBlock(Sec, Content,
                                   orc::ExecutorAddr(~uint64_t(7)),
                                   /*Alignment=*/1, /*AlignmentOffset=*/0);
    B.addEdge(x86_64::Pointer64, /*Offset=*/2, PtrSym, /*Addend=*/0);
    return G.addAnonymousSymbol(B, /*Offset=*/0,
                                /*Size=*/sizeof(StubBytes_x86_64),
                                /*IsCallable=*/true, /*IsLive=*/false);
}
#else
static Symbol &createCCallStub(LinkGraph &G, Section &Sec, Symbol &PtrSym) {
    return jitlink::getPointerJumpStubCreator(G.getTargetTriple())(G, Sec, PtrSym);
}
#endif

#endif

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

namespace {

// Allocate an immutable content block holding `s` plus a NUL terminator.
// Returns the symbol naming the start of the string.
Symbol &emitCString(LinkGraph &G, Section &Sec, const char *s) {
    size_t len = std::strlen(s) + 1;
    auto Buf = G.allocateContent(ArrayRef<char>(s, len));
    auto &B = G.createContentBlock(Sec, Buf, orc::ExecutorAddr(~uint64_t(0)),
                                   /*Alignment=*/1, /*AlignmentOffset=*/0);
    return G.addAnonymousSymbol(B, /*Offset=*/0, len,
                                /*IsCallable=*/false, /*IsLive=*/true);
}

} // namespace

// ---------------------------------------------------------------------------
// StubMU: per-spec MaterializationUnit.
//
// On materialization, builds a fresh LinkGraph containing the stub, ptr slot,
// trampoline, data struct, and string constants for the spec, then submits
// it to the ObjectLinkingLayer. The stub *and* the slot are exported as
// named symbols (via `Entry.StubName` / `Entry.SlotName`) so both ccall
// callers (which branch through the stub) and cglobal callers (which load
// from the slot directly) can be served by the same MU.
// ---------------------------------------------------------------------------

class CSymbolStubManager::StubMU : public MaterializationUnit {
public:
    StubMU(CSymbolStubManager &Mgr, Entry E, jl_ccall_spec_t Spec)
      : MaterializationUnit(makeInterface(E)),
        Mgr(Mgr), E(std::move(E)), Spec(std::move(Spec)) {}

    StringRef getName() const override { return "JuliaCSymbolStubMU"; }

private:
    void materialize(std::unique_ptr<MaterializationResponsibility> MR) override {
        Mgr.emitGraph(std::move(MR), E, Spec);
    }

    void discard(const JITDylib &, const SymbolStringPtr &) override {
        // No state to discard — graph is built only on materialize.
    }

    static Interface makeInterface(const Entry &E) {
        SymbolFlagsMap F;
        F[E.StubName] = JITSymbolFlags::Callable | JITSymbolFlags::Exported;
        F[E.SlotName] = JITSymbolFlags::Exported;
        return Interface(F, /*InitSym=*/SymbolStringPtr{});
    }

    CSymbolStubManager &Mgr;
    Entry E;
    jl_ccall_spec_t Spec;
};

// ---------------------------------------------------------------------------
// CSymbolStubManager
// ---------------------------------------------------------------------------

Expected<std::unique_ptr<CSymbolStubManager>>
CSymbolStubManager::Create(ObjectLinkingLayer &OLL, JITDylib &JD) {
    auto &ES = OLL.getExecutionSession();
    // Long-lived ResourceTracker. Stubs/trampolines/ptrs are pinned for the
    // JIT's lifetime; they're never torn down today.
    auto RT = JD.createResourceTracker();
    auto ResolverName = ES.intern("__ccall_reentry_trampoline");
    return std::make_unique<CSymbolStubManager>(OLL, JD, std::move(RT),
                                                std::move(ResolverName));
}

CSymbolStubManager::CSymbolStubManager(ObjectLinkingLayer &OLL_, JITDylib &JD_,
                                       ResourceTrackerSP RT_,
                                       SymbolStringPtr ResolverName_)
  : JD(JD_), ES(OLL_.getExecutionSession()), OLL(OLL_),
    RT(std::move(RT_)), ResolverName(std::move(ResolverName_)) {}

CSymbolStubManager::Entry &
CSymbolStubManager::getOrCreateLocked(const jl_ccall_spec_t &Spec, bool &Registered) JL_NOTSAFEPOINT {
    auto It = SpecEntries.find(Spec);
    if (It != SpecEntries.end()) {
        Registered = false;
        return It->second;
    }
    auto id = std::to_string(NextId++);
    auto [Inserted, _] = SpecEntries.try_emplace(
        Spec, Entry{ES.intern("$csymbol$stub$" + id), ES.intern("$csymbol$slot$" + id)});
    Registered = true;
    return Inserted->second;
}

SymbolStringPtr CSymbolStubManager::getOrCreateStub(const jl_ccall_spec_t &Spec) JL_NOTSAFEPOINT {
    bool needRegister = false;
    SymbolStringPtr Stub, Slot;
    {
        std::lock_guard<std::mutex> L(Mtx);
        Entry &E = getOrCreateLocked(Spec, needRegister);
        Stub = E.StubName;
        Slot = E.SlotName;
        if (needRegister) {
            cantFail(JD.define(std::make_unique<StubMU>(*this, E, Spec), RT));
        }
    }
    return Stub;
}

SymbolStringPtr CSymbolStubManager::getOrCreateSlot(const jl_ccall_spec_t &Spec) JL_NOTSAFEPOINT {
    bool needRegister = false;
    SymbolStringPtr Stub, Slot;
    {
        std::lock_guard<std::mutex> L(Mtx);
        Entry &E = getOrCreateLocked(Spec, needRegister);
        Stub = E.StubName;
        Slot = E.SlotName;
        if (needRegister) {
            cantFail(JD.define(std::make_unique<StubMU>(*this, E, Spec), RT));
        }
    }
    return Slot;
}

// ---------------------------------------------------------------------------
// Graph emission.
//
// Per-spec LinkGraph layout:
//
//   .__ccall_stubs    (R+X)   stub:  jump through ptr          [exported]
//   .__ccall_ptrs     (R+W)   ptr:   .quad &tramp  (initial)  [exported]
//   .__ccall_tramps   (R+X)   tramp: push &data; jump to resolver
//   .__ccall_data     (R)     data:  csymbol_data_t struct
//                              libstr / funcstr (string blocks)
//
// The stub and the ptr slot are exported under canonical names from `E`
// (StubName, SlotName) so ccall and cglobal callers can find them by name
// in the JITDylib. The trampoline, data struct, and auxiliary string
// blocks remain anonymous — they're reachable internally via JITLink edges.
// ---------------------------------------------------------------------------
void CSymbolStubManager::emitGraph(std::unique_ptr<MaterializationResponsibility> MR,
                                   const Entry &E,
                                   const jl_ccall_spec_t &Spec) {
    auto G = std::make_unique<LinkGraph>(
        ("<csymbol_stub:" + std::string(*E.StubName) + ">"),
        ES.getSymbolStringPool(), ES.getTargetTriple(), SubtargetFeatures(),
        getGenericEdgeKindName);

    auto &StubSec  = G->createSection("$__ccall_stubs",
                                      orc::MemProt::Read | orc::MemProt::Exec);
    auto &PtrSec   = G->createSection("$__ccall_ptrs",
                                      orc::MemProt::Read | orc::MemProt::Write);
    auto &TrampSec = G->createSection("$__ccall_tramps",
                                      orc::MemProt::Read | orc::MemProt::Exec);
    auto &DataSec  = G->createSection("$__ccall_data",
                                      orc::MemProt::Read);

    // String constants. Spec.lib is `void *` because it may be one of the
    // JL_*_LIBNAME sentinels (cast from const char* of (1), (2), (3)) or an
    // interned string. The resolver passes it through to jl_get_library_,
    // which handles the sentinels. Either way we treat it as a const char*.
    //
    // For sentinels we don't allocate string content (the value is the int);
    // we encode it as an absolute symbol pointing at the integer value.
    Symbol *LibStrSym = nullptr;
    if (Spec.lib) {
        uintptr_t libVal = reinterpret_cast<uintptr_t>(Spec.lib);
        if (libVal <= 3) {
            // Sentinel — encode as an absolute symbol equal to the sentinel value.
            LibStrSym = &G->addAbsoluteSymbol(
                G->allocateName("lib_sentinel"),
                orc::ExecutorAddr(libVal), /*Size=*/0,
                Linkage::Strong, Scope::Local, /*IsLive=*/false);
        } else {
            LibStrSym = &emitCString(*G, DataSec,
                                     static_cast<const char*>(Spec.lib));
        }
    }
    // Func string: optional. NULL when codegen couldn't statically resolve
    // the function name; the resolver pulls it out of `target` instead.
    Symbol *FuncStrSym = nullptr;
    if (Spec.func) {
        FuncStrSym = &emitCString(*G, DataSec, Spec.func);
    }

    // target: an 8-byte slot whose contents = address of the rooted
    // jl_value_t svec. Matches the AOT shape (literal_pointer_val_slot in
    // cgutils.cpp) — `data->target` always points at a slot that contains
    // the value's address, and the resolver derefs once to get the value.
    // This keeps the data-struct ABI uniform across JIT and AOT compiles.
    Symbol *TargetSlotSym = nullptr;
    if (Spec.target) {
        // Absolute symbol whose address IS the target svec's address.
        Symbol &TargetValueAbs = G->addAbsoluteSymbol(
            G->allocateName("target_value_v"),
            orc::ExecutorAddr::fromPtr(Spec.target),
            /*Size=*/8,
            Linkage::Strong, Scope::Local, /*IsLive=*/false);
        // Mutable 8-byte slot block; JITLink fixes its content to
        // TargetValueAbs's address via a Pointer64 edge.
        auto &SlotBlock = G->createMutableContentBlock(
            DataSec, /*ContentSize=*/8,
            orc::ExecutorAddr(~uint64_t(7)),
            /*Alignment=*/8, /*AlignmentOffset=*/0);
        SlotBlock.addEdge(getPointer64Kind(), /*Offset=*/0,
                          TargetValueAbs, /*Addend=*/0);
        TargetSlotSym = &G->addAnonymousSymbol(SlotBlock, /*Offset=*/0,
                                               /*Size=*/8,
                                               /*IsCallable=*/false,
                                               /*IsLive=*/false);
    }

    // The data struct: 32 bytes of zero-initialized backing storage that
    // JITLink will fix up via up to four Pointer64 edges. Layout matches
    // csymbol_data_t: { ptr_slot, lib, func, target }.
    auto &DataBlock = G->createMutableContentBlock(
        DataSec, /*ContentSize=*/32, orc::ExecutorAddr(~uint64_t(7)),
        /*Alignment=*/8, /*AlignmentOffset=*/0);
    auto &DataSym = G->addAnonymousSymbol(DataBlock, /*Offset=*/0, /*Size=*/32,
                                          /*IsCallable=*/false, /*IsLive=*/true);

    // Trampoline: pushes &data on the stack and tail-branches to
    // ccall_reentry_trampoline (see emitCCallTrampoline). The resolver is an
    // external symbol resolved through the JD (it's registered as an
    // absolute symbol pointing at our libjulia-internal function).
    auto &ResolverSym = G->addExternalSymbol(*ResolverName,
                                             /*Size=*/0,
                                             /*WeakReferenced=*/false);
    auto &TrampBlock = emitCCallTrampoline(*G, TrampSec, DataSym, ResolverSym);
    auto &TrampSym = G->addAnonymousSymbol(TrampBlock, /*Offset=*/0,
                                           /*Size=*/TrampBlock.getSize(),
                                           /*IsCallable=*/true,
                                           /*IsLive=*/true);

    // Pointer slot: 8 bytes initialized via Pointer64 edge to trampoline.
    // Exported under E.SlotName so cglobal callers can look it up by name
    // in the JITDylib (their inline diamond loads from / stores to this
    // very slot).
    auto &PtrSym = createCCallPtrSlot(*G, PtrSec, TrampSym);
    PtrSym.setName(E.SlotName);
    PtrSym.setScope(Scope::Default);
    PtrSym.setLinkage(Linkage::Strong);

    // Fill in data's pointer fields. ptr_slot (offset 0) is mandatory;
    // others are emitted only when the corresponding spec field is set.
    DataBlock.addEdge(getPointer64Kind(), /*Offset=*/0,  PtrSym,
                      /*Addend=*/0);
    if (LibStrSym) {
        DataBlock.addEdge(getPointer64Kind(), /*Offset=*/8,
                          *LibStrSym, /*Addend=*/0);
    }
    if (FuncStrSym) {
        DataBlock.addEdge(getPointer64Kind(), /*Offset=*/16,
                          *FuncStrSym, /*Addend=*/0);
    }
    if (TargetSlotSym) {
        DataBlock.addEdge(getPointer64Kind(), /*Offset=*/24,
                          *TargetSlotSym, /*Addend=*/0);
    }

    // Stub: indirect jump through PtrSym (per-arch byte template).
    auto &StubSym = createCCallStub(*G, StubSec, PtrSym);
    StubSym.setName(E.StubName);
    StubSym.setScope(Scope::Default);
    StubSym.setLinkage(Linkage::Strong);

    OLL.emit(std::move(MR), std::move(G));
}

} // namespace csymbol
} // namespace julia

// (ccall_resolve_and_patch is defined in ccall_runtime.cpp, which is
// compiled into libjulia-internal so pkgimages can link against it.)
