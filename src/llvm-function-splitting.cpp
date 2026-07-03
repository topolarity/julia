// This file is a part of Julia. License is MIT: https://julialang.org/license

// FunctionSplittingPass: bound the size of functions and basic blocks reaching
// the middle/back end, to avoid super-linear scaling in GVN, LateLowerGCFrame,
// loop analyses, instruction selection, register allocation and basic block
// placement.
//
// The pass works in three steps:
//   1. Oversized basic blocks are chunked at low-live-count cut points
//      (normalization; creates the block boundaries step 2 needs).
//   2. Regions are formed by interval growing: starting from a seed block,
//      blocks whose predecessors all lie inside the group are added until the
//      group's escape edges converge on a single join block whose
//      predecessors are all inside. That join is split into a tiny
//      caller-resident "boundary" block (PHIs, spill fills/reloads and
//      rematerialized derivations live there) and a body block that seeds the
//      next region. Cold edges (e.g. into shared throw blocks) may leave a
//      region; they simply become additional exits of the outlined function.
//   3. Each region is outlined with CodeExtractor.
//
// This pass must run before LateLowerGCFrame: while tracked pointers are still
// SSA values in addrspace(10), outlined callees get correct GC frames
// automatically because
//   * tracked (AS10) arguments are treated as rooted by the caller for the
//     duration of the call (LateLowerGCFrame numbers Arguments -1), and the
//     caller keeps call operands in its own live set across the callsite,
//   * the call to the outlined function is an ordinary safepoint, so the
//     caller re-roots everything live across the split point,
//   * static allocas of `ptr addrspace(10)` (which CodeExtractor uses to
//     return outputs) are turned into GC frame slots in the caller.
//
// The correctness-relevant interface of each region (live-ins/live-outs) is
// computed exactly from SSA def-use chains; the block-local liveness counts
// used for intra-block cut points are advisory only.
//
// Boundary rules enforced here:
//   * values in AS11 (Derived) or AS13 (Loaded) may be *inputs* of a region
//     (an Argument is assumed parent-rooted), but must not be *outputs*;
//     derivation spines (GEP/addrspacecast/julia.gc_loaded) are instead
//     rematerialized in the boundary block after the region,
//   * AS12 (CalleeRooted) values must not cross at all: the caller drops them
//     from safepoint live sets assuming the callee roots them, which an
//     outlined function does not,
//   * token values (gc_preserve_begin/end) cannot cross a function boundary,
//   * `returns_twice` calls (exception handler entry) and handler push/pop
//     stay in the original frame,
//   * aggregates or vectors containing tracked pointers may be inputs but not
//     outputs (their output allocas would not be recognized as GC frame slots
//     by the caller's GC lowering).
//
// The pass is a no-op unless -julia-split-block-threshold or
// -julia-split-function-threshold is set nonzero.

#include "llvm-version.h"
#include "passes.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/ADT/SetVector.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/Statistic.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/CodeExtractor.h>
#include <llvm/Transforms/Utils/ValueMapper.h>

#include <chrono>

#include "llvm-codegen-shared.h"
#include "llvm-pass-helpers.h"

#define DEBUG_TYPE "julia-function-splitting"

using namespace llvm;

STATISTIC(BlocksChunked, "Number of oversized basic blocks chunked");
STATISTIC(RegionsFormed, "Number of multi-block regions formed");
STATISTIC(SupersFormed, "Number of hierarchical super-regions formed");
STATISTIC(RegionsExtracted, "Number of regions outlined into new functions");
STATISTIC(RegionsSpilled, "Number of regions whose interface was spilled through memory");

static cl::opt<unsigned> SplitBlockThreshold(
    "julia-split-block-threshold", cl::init(0), cl::Hidden,
    cl::desc("Chunk basic blocks with more instructions than this and outline the "
             "containing function's regions (0 = disabled)"));

static cl::opt<unsigned> SplitFunctionThreshold(
    "julia-split-function-threshold", cl::init(0), cl::Hidden,
    cl::desc("Outline chunk-sized regions from functions with more instructions "
             "than this (0 = disabled)"));

static cl::opt<unsigned> SplitChunkSize(
    "julia-split-chunk-size", cl::init(1000), cl::Hidden,
    cl::desc("Target instruction count of outlined regions"));

// Debugging kill-switches for isolating miscompiles.
static cl::opt<bool> SplitNoHoistRemat(
    "julia-split-no-hoist-remat", cl::init(false), cl::Hidden,
    cl::desc("Disable preheader-hoisted rematerialization"));
static cl::opt<bool> SplitNoSiteRemat(
    "julia-split-no-site-remat", cl::init(false), cl::Hidden,
    cl::desc("Disable per-use-site rematerialization"));
static cl::opt<bool> SplitNoInputSpill(
    "julia-split-no-input-spill", cl::init(false), cl::Hidden,
    cl::desc("Disable spilling of region inputs"));
static cl::opt<bool> SplitNoOutputSpill(
    "julia-split-no-output-spill", cl::init(false), cl::Hidden,
    cl::desc("Disable spilling of region outputs"));

static cl::opt<int> SplitSpillMax(
    "julia-split-spill-max", cl::init(-1), cl::Hidden,
    cl::desc("Only spill the first N regions that request it (-1 = unlimited)"));

static cl::opt<bool> SplitDebug(
    "julia-split-debug", cl::init(false), cl::Hidden,
    cl::desc("Print region formation/rejection diagnostics (note: printing "
             "instructions builds a module slot tracker and is very slow on "
             "big modules)"));

static cl::opt<bool> SplitTime(
    "julia-split-time", cl::init(false), cl::Hidden,
    cl::desc("Print per-stage timing for the pass"));

static cl::opt<unsigned> SplitGroupSize(
    "julia-split-group-size", cl::init(24), cl::Hidden,
    cl::desc("Number of regions grouped into each parent of the hierarchical "
             "decomposition (0 = flat splitting)"));

static cl::opt<unsigned> SplitDirectArgLimit(
    "julia-split-direct-arg-limit", cl::init(64), cl::Hidden,
    cl::desc("Maximum region interface size passed directly as arguments/output "
             "pointers before spilling through in-memory aggregates"));
static cl::opt<bool> SplitSingleExitCuts(
    "julia-split-single-exit-cuts", cl::init(false), cl::Hidden,
    cl::desc("Prefer region cuts where exactly one non-cold escape target "
             "remains: such regions need no exit selector in the caller "
             "(diagnostic knob for measuring the selector's runtime share; "
             "cold escapes such as throw paths still produce exits)"));
static cl::opt<unsigned> SplitMaxRegionBlocks(
    "julia-split-max-region-blocks", cl::init(4096), cl::Hidden,
    cl::desc("Maximum number of basic blocks a region may absorb (bounds the "
             "growth scan). Regions that hit this clamp cut at the best legal "
             "point instead of the size target; clamp cuts are counted and "
             "reported under -julia-split-time so parameter sweeps see the "
             "realized region sizes rather than the requested target"));
static cl::opt<unsigned> SplitOutputSpillMin(
    "julia-split-output-spill-min", cl::init(2), cl::Hidden,
    cl::desc("Spill region outputs through the aggregate whenever a region has "
             "at least this many (0 = only with the full wide-interface spill). "
             "Contiguous slots let one pointer replace per-output pointer "
             "arguments and keep the marshalling vectorizable"));
static cl::opt<unsigned> SplitPrefetchLines(
    "julia-split-prefetch-lines", cl::init(0), cl::Hidden,
    cl::desc("EXPERIMENT(boundary-tax): before each region call, software-"
             "prefetch the first N 64-byte lines of the NEXT region's code "
             "into the unified L2 (x86 cannot prefetch into L1i), so region "
             "entries hit L2 instead of demand-missing to L3 (0 = off)"));

namespace {

// Sub-stage accumulators (diagnostics; printed under -julia-split-debug).
static int64_t RematScanUs, RematCollectUs, RematHoistUs, RematSiteUs;
static int64_t HoistCalls, BoundaryCalls, EscapingRoots;

// How a value's type behaves at a region boundary.
enum class ValKind {
    Untracked,    // no GC-relevant pointers: legal input and output
    Tracked,      // scalar ptr addrspace(10): legal input and output
    Derived,      // scalar AS11/AS13: legal input, must be rematerialized as output
    CalleeRooted, // scalar AS12: must not cross
    TokenLike,    // token: must not cross
    Mixed,        // aggregate/vector containing tracked pointers: input only
};

static ValKind classifyType(Type *T) JL_NOTSAFEPOINT
{
    if (T->isTokenTy())
        return ValKind::TokenLike;
    if (T->isPtrOrPtrVectorTy()) {
        unsigned AS = T->getPointerAddressSpace();
        if (AS == AddressSpace::Tracked)
            return T->isVectorTy() ? ValKind::Mixed : ValKind::Tracked;
        if (AS == AddressSpace::Derived || AS == AddressSpace::Loaded)
            return T->isVectorTy() ? ValKind::Mixed : ValKind::Derived;
        if (AS == AddressSpace::CalleeRooted)
            return ValKind::CalleeRooted;
        return ValKind::Untracked;
    }
    if (T->isAggregateType()) {
        CountTrackedPointers ctp(T);
        if (ctp.count == 0)
            return ValKind::Untracked;
        return ValKind::Mixed;
    }
    return ValKind::Untracked;
}

// Instructions that must remain in the original function frame.
static bool isPinned(Instruction &I, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    if (isa<AllocaInst>(I) || I.isEHPad())
        return true;
    if (I.getType()->isTokenTy())
        return true;
    for (Value *Op : I.operands())
        if (Op->getType()->isTokenTy())
            return true;
    if (auto *CI = dyn_cast<CallBase>(&I)) {
        // setjmp for the exception runtime: a longjmp must never target a
        // frame that has already returned.
        if (CI->hasFnAttr(Attribute::ReturnsTwice))
            return true;
        // A "julia.return_roots" buffer must be an alloca in the same function
        // as the callsite (LateLowerGCFrame registers it as a GC frame array
        // and aborts otherwise), and it must outlive every read of the
        // associated sret aggregate. Keeping the callsite in the parent, next
        // to the buffer codegen allocated in the entry block, satisfies both.
        for (unsigned i = 0; i < CI->arg_size(); ++i) {
            if (CI->getAttributes().getParamAttr(i, "julia.return_roots").isValid())
                return true;
        }
        if (auto *II = dyn_cast<IntrinsicInst>(&I)) {
            switch (II->getIntrinsicID()) {
            case Intrinsic::stacksave:
            case Intrinsic::stackrestore:
            case Intrinsic::frameaddress:
            case Intrinsic::returnaddress:
            case Intrinsic::vastart:
            case Intrinsic::vaend:
            case Intrinsic::vacopy:
                return true;
            default:
                break;
            }
        }
        if (Function *Callee = CI->getCalledFunction()) {
            if (Callee == ctx.gc_preserve_begin_func || Callee == ctx.gc_preserve_end_func ||
                Callee == ctx.pgcstack_getter || Callee == ctx.adoptthread_func)
                return true;
            // Exception-handler state calls (marked at their declaration by
            // codegen) restore snapshots taken at handler entry under the
            // precondition that GC-frame pushes since then have been popped;
            // an outlined callee's own GC frame prologue violates that, so
            // they must stay in the invocation that entered the handler.
            if (Callee->hasFnAttribute("julia.eh_state"))
                return true;
        }
    }
    if (auto *SI = dyn_cast<StoreInst>(&I)) {
        // Storing tracked values into a stack slot is only recognized by the
        // caller's GC lowering when the slot is an all-tracked alloca (which
        // becomes a GC frame slot) or when the store itself is visible to that
        // function's lowering. Keep any other tracked store in the caller.
        Type *VTy = SI->getValueOperand()->getType();
        if (CountTrackedPointers(VTy).count > 0) {
            const Value *Base = getUnderlyingObject(SI->getPointerOperand());
            if (auto *AI = dyn_cast<AllocaInst>(Base)) {
                // All-tracked static allocas become GC frame slots in the
                // caller unconditionally (see LateLowerGCFrame), so stores
                // into them may move into the callee. Anything else must stay
                // with the caller-side lowering that tracks it.
                auto tracked = CountTrackedPointers(AI->getAllocatedType());
                if (!(AI->isStaticAlloca() && tracked.count && tracked.all && !tracked.derived))
                    return true;
            }
            else if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
                return true;
            }
        }
    }
    return false;
}

// A single-entry group of blocks with one designated continue-target
// ("boundary") that stays in the caller. Cold edges to other outside blocks
// are permitted (CodeExtractor turns them into extra exits).
struct Region {
    SmallVector<BasicBlock *, 16> Blocks; // Blocks[0] is the entry
    SmallPtrSet<BasicBlock *, 32> Set;
    BasicBlock *Boundary = nullptr;
    unsigned Insts = 0;
    // Whether every predecessor of Boundary was inside the region when it was
    // formed (i.e. the extracted call will dominate the boundary). Boundary
    // rematerialization requires this; spilling does not.
    bool BoundaryDominated = false;
};

// Lazily computed per-block size and pinnedness (blocks are created during
// splitting, so this must tolerate new blocks).
struct BlockInfoCache {
    const JuliaPassContext &ctx;
    DenseMap<BasicBlock *, std::pair<unsigned, bool>> M;
    BlockInfoCache(const JuliaPassContext &ctx) JL_NOTSAFEPOINT : ctx(ctx) {}
    std::pair<unsigned, bool> get(BasicBlock *BB) JL_NOTSAFEPOINT
    {
        auto It = M.find(BB);
        if (It != M.end())
            return It->second;
        unsigned n = 0;
        bool pinned = false;
        for (Instruction &I : *BB) {
            n++;
            if (!pinned && isPinned(I, ctx))
                pinned = true;
        }
        return M[BB] = {n, pinned};
    }
    void invalidate(BasicBlock *BB) JL_NOTSAFEPOINT { M.erase(BB); }

    // A block is cold if every path from it ends in `unreachable` (throw
    // paths). Cold escape targets don't compete for the continue-target slot.
    DenseMap<BasicBlock *, char> ColdCache;
    bool isCold(BasicBlock *BB, unsigned Depth = 0) JL_NOTSAFEPOINT
    {
        auto It = ColdCache.find(BB);
        if (It != ColdCache.end())
            return It->second == 1;
        if (Depth > 32)
            return false; // don't recurse forever; hot paths are long
        ColdCache[BB] = 2; // cycle guard: treat as not-cold while in progress
        bool cold;
        if (isa<UnreachableInst>(BB->getTerminator())) {
            cold = true;
        }
        else if (succ_empty(BB)) {
            cold = false; // ret
        }
        else {
            cold = true;
            for (BasicBlock *S : successors(BB)) {
                if (!isCold(S, Depth + 1)) {
                    cold = false;
                    break;
                }
            }
        }
        ColdCache[BB] = cold ? 1 : 0;
        return cold;
    }
};

// The location of a use for dominance purposes: a PHI's use happens at the end
// of its incoming block.
static BasicBlock *useBlock(Use &U) JL_NOTSAFEPOINT
{
    auto *UI = cast<Instruction>(U.getUser());
    if (auto *PN = dyn_cast<PHINode>(UI))
        return PN->getIncomingBlock(U);
    return UI->getParent();
}

// The unique caller-resident block that unconditionally flows into the
// region's entry (ignoring region-internal backedges when the region contains
// a loop). Spill fills and hoisted rematerializations are placed here.
static BasicBlock *regionPreheader(const Region &R,
                                   const SmallPtrSetImpl<BasicBlock *> &Owned) JL_NOTSAFEPOINT
{
    BasicBlock *Entry = R.Blocks[0];
    BasicBlock *Pred = nullptr;
    for (BasicBlock *P : predecessors(Entry)) {
        if (R.Set.count(P))
            continue; // backedge
        if (Pred && Pred != P)
            return nullptr;
        Pred = P;
    }
    if (!Pred || Pred->getSingleSuccessor() != Entry || Owned.count(Pred))
        return nullptr;
    return Pred;
}

static const unsigned RematSpineLimit = 32;

// Loads of immutable fields of GC-managed memory (e.g. an array's data
// pointer). These may be duplicated and speculated: the address comes from a
// live managed object, so the memory is readable and the value cannot change.
static bool isImmutableManagedLoad(LoadInst *LI) JL_NOTSAFEPOINT
{
    // Unordered atomic loads (how Julia emits object field loads) can be
    // duplicated like plain loads.
    if (!LI->isUnordered())
        return false;
    bool Immut = LI->getMetadata(LLVMContext::MD_invariant_load) != nullptr;
    if (!Immut) {
        MDNode *TBAA = LI->getMetadata(LLVMContext::MD_tbaa);
        while (TBAA && TBAA->getNumOperands() > 1) {
            auto *S = dyn_cast<MDString>(TBAA->getOperand(0));
            if (S) {
                StringRef Name = S->getString();
                if (Name == "jtbaa_immut" || Name == "jtbaa_const" ||
                    Name == "jtbaa_datatype" || Name == "jtbaa_memoryptr" ||
                    Name == "jtbaa_memorylen" || Name == "jtbaa_memoryown") {
                    Immut = true;
                    break;
                }
            }
            TBAA = dyn_cast<MDNode>(TBAA->getOperand(1));
        }
    }
    if (!Immut)
        return false;
    // Speculation also needs the address to be dereferenceable: fields of a
    // live managed object are, and so are global slots.
    unsigned AS = LI->getPointerOperand()->getType()->getPointerAddressSpace();
    if (AS == AddressSpace::Tracked || AS == AddressSpace::Derived ||
        AS == AddressSpace::Loaded)
        return true;
    return isa<GlobalValue>(getUnderlyingObject(LI->getPointerOperand()));
}

static bool isSpineClonable(Instruction *I, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    if (isa<GetElementPtrInst>(I) || isa<AddrSpaceCastInst>(I) || isa<BitCastInst>(I))
        return true;
    if (auto *CI = dyn_cast<CallInst>(I))
        return ctx.gc_loaded_func && CI->getCalledFunction() == ctx.gc_loaded_func;
    return false;
}

// Collect (operands-first) the full clone-spine needed to recompute I at the
// end of Pred, before the region: every in-region dependency must itself be
// clonable (address computations and immutable managed loads), and every
// out-of-region dependency must dominate Pred.
static bool collectHoistSpine(Instruction *I, const Region &R, BasicBlock *Pred,
                              const DominatorTree &DT,
                              SmallVectorImpl<Instruction *> &Spine,
                              SmallPtrSetImpl<Instruction *> &Visited,
                              const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    HoistCalls++;
    if (Visited.count(I))
        return true;
    if (Spine.size() >= RematSpineLimit)
        return false;
    bool CloneOK = isSpineClonable(I, ctx);
    if (!CloneOK)
        if (auto *LI = dyn_cast<LoadInst>(I))
            CloneOK = isImmutableManagedLoad(LI);
    if (!CloneOK) {
        if (SplitDebug)
            errs() << "julia-function-splitting: hoist not-clonable: " << *I << "\n";
        return false;
    }
    for (Value *Op : I->operands()) {
        auto *OpI = dyn_cast<Instruction>(Op);
        if (!OpI)
            continue;
        if (R.Set.count(OpI->getParent())) {
            if (!collectHoistSpine(OpI, R, Pred, DT, Spine, Visited, ctx))
                return false;
        }
        else if (!DT.dominates(OpI->getParent(), Pred) && OpI->getParent() != Pred) {
            if (SplitDebug)
                errs() << "julia-function-splitting: hoist op-dom: " << *OpI << "\n";
            return false;
        }
    }
    Visited.insert(I);
    Spine.push_back(I);
    return true;
}

// Collect (operands-first) the derived-typed spine needed to recompute I in
// the boundary block after the region. Tracked/untracked in-region operands
// stay behind as ordinary region outputs (extraction rewrites the clone's
// references to the caller-side reloads).
static bool collectBoundarySpine(Instruction *I, const Region &R,
                                 SmallVectorImpl<Instruction *> &Spine,
                                 SmallPtrSetImpl<Instruction *> &Visited,
                                 const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    BoundaryCalls++;
    if (Visited.count(I))
        return true;
    if (Spine.size() >= RematSpineLimit)
        return false;
    if (!isSpineClonable(I, ctx))
        return false;
    for (Value *Op : I->operands()) {
        auto *OpI = dyn_cast<Instruction>(Op);
        if (!OpI || !R.Set.count(OpI->getParent()))
            continue;
        ValKind K = classifyType(OpI->getType());
        if (K == ValKind::Tracked || K == ValKind::Untracked)
            continue;
        if (K != ValKind::Derived)
            return false;
        if (!collectBoundarySpine(OpI, R, Spine, Visited, ctx))
            return false;
    }
    Visited.insert(I);
    Spine.push_back(I);
    return true;
}

// Rewrite uses outside R of derived pointers defined in R to rematerialized
// clones of their derivation spine. Chains recomputable before the region are
// hoisted into the region preheader (dominating every use). Everything else is
// rematerialized at each external use site: the spine's in-region roots
// (tracked or untracked values that can't be cloned, e.g. fresh allocations or
// mutable loads) are routed through stack slots written right after their
// defs, so a clone anywhere the original value was live reads back the right
// value; tracked slots become GC frame slots in the caller. Returns false
// (without modifying anything) if some derived value escapes R and cannot be
// rematerialized; the region must then stay in the caller.
static bool rematerializeDerivedOutputs(Function &F, Region &R, const DominatorTree &DT,
                                        const SmallPtrSetImpl<BasicBlock *> &Owned,
                                        const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    auto rnow = []() JL_NOTSAFEPOINT { return std::chrono::steady_clock::now(); };
    auto rus = [](auto a, auto b) JL_NOTSAFEPOINT {
        return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count();
    };
    auto R0 = rnow();
    SmallVector<Instruction *, 8> Escaping;
    for (BasicBlock *BB : R.Blocks) {
        for (Instruction &I : *BB) {
            if (classifyType(I.getType()) != ValKind::Derived)
                continue;
            for (User *U : I.users()) {
                if (!R.Set.count(cast<Instruction>(U)->getParent())) {
                    Escaping.push_back(&I);
                    break;
                }
            }
        }
    }
    RematScanUs += rus(R0, rnow());
    if (Escaping.empty())
        return true;
    // Hoisted clones are SSA values: they must not land inside another
    // region, whose extraction would turn them into illegal derived outputs
    // (regionPreheader excludes owned blocks).
    BasicBlock *Pred = regionPreheader(R, Owned);

    // Validate everything before mutating anything.
    auto R1 = rnow();
    SmallVector<Instruction *, RematSpineLimit> HoistSpine, SiteSpine;
    SmallPtrSet<Instruction *, 16> HoistSet, SiteSet;
    EscapingRoots += Escaping.size();
    for (Instruction *I : Escaping) {
        if (Pred && collectHoistSpine(I, R, Pred, DT, HoistSpine, HoistSet, ctx))
            continue;
        if (SplitNoSiteRemat || !collectBoundarySpine(I, R, SiteSpine, SiteSet, ctx)) {
            if (SplitDebug)
                errs() << "julia-function-splitting: remat spine fail: " << *I << "\n";
            return false;
        }
    }
    // The site spine's in-region roots must be routable through stack slots.
    SmallSetVector<Instruction *, 8> RoutedOps;
    for (Instruction *I : SiteSpine) {
        for (Value *Op : I->operands()) {
            auto *OpI = dyn_cast<Instruction>(Op);
            if (!OpI || SiteSet.count(OpI) || !R.Set.count(OpI->getParent()))
                continue;
            ValKind K = classifyType(OpI->getType());
            if (K == ValKind::Tracked ||
                (K == ValKind::Untracked && OpI->getType()->isFirstClassType() &&
                 OpI->getType()->isSized())) {
                RoutedOps.insert(OpI);
            }
            else {
                if (SplitDebug)
                    errs() << "julia-function-splitting: remat root fail: " << *OpI << "\n";
                return false;
            }
        }
    }

    RematCollectUs += rus(R1, rnow());
    LLVMContext &Ctx = F.getContext();
    Type *T_prjlvalue = PointerType::get(Ctx, AddressSpace::Tracked);
    auto R2 = rnow();
    if (!HoistSpine.empty()) {
        // RF_NoModuleLevelChanges below (and in the site clones): only remap
        // the local operands through the map. Without it the mapper also
        // "remaps" the !dbg attachment, cloning the (distinct)
        // DISubprogram/DICompileUnit it is rooted at and leaving the clone's
        // location pointing at a duplicate subprogram, which breaks debug
        // info validity for the whole function.
        ValueToValueMapTy VMap;
        BasicBlock::iterator IP = Pred->getTerminator()->getIterator();
        for (Instruction *I : HoistSpine) {
            Instruction *Clone = I->clone();
            Clone->setName(I->getName() + ".remat");
            Clone->insertBefore(IP);
            RemapInstruction(Clone, VMap,
                             RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
            VMap[I] = Clone;
        }
        // The clones dominate the whole region and everything after it: take
        // over all uses; the originals become dead.
        for (Instruction *I : HoistSpine)
            I->replaceAllUsesWith(cast<Instruction>(VMap[I]));
    }
    RematHoistUs += rus(R2, rnow());
    auto R3 = rnow();
    if (!SiteSpine.empty()) {
        // Route the roots through slots.
        IRBuilder<> EB(&F.getEntryBlock(), F.getEntryBlock().begin());
        DenseMap<Instruction *, AllocaInst *> Slot;
        for (Instruction *OpI : RoutedOps) {
            bool Tracked = classifyType(OpI->getType()) == ValKind::Tracked;
            AllocaInst *A =
                Tracked ? EB.CreateAlloca(T_prjlvalue, nullptr, OpI->getName() + ".gcslot")
                        : EB.CreateAlloca(OpI->getType(), nullptr, OpI->getName() + ".slot");
            if (Tracked)
                A->setAlignment(Align(sizeof(void *)));
            Slot[OpI] = A;
            BasicBlock::iterator SP = isa<PHINode>(OpI)
                                          ? OpI->getParent()->getFirstInsertionPt()
                                          : std::next(OpI->getIterator());
            IRBuilder<> SB(OpI->getParent(), SP);
            SB.CreateStore(OpI, A);
        }
        // Rematerialize at each external use site.
        for (Instruction *I : SiteSpine) {
            SmallVector<Use *, 8> ExtUses;
            for (Use &U : I->uses())
                if (!R.Set.count(useBlock(U)))
                    ExtUses.push_back(&U);
            for (Use *U : ExtUses) {
                auto *UI = cast<Instruction>(U->getUser());
                BasicBlock::iterator IP;
                if (auto *PN = dyn_cast<PHINode>(UI))
                    IP = PN->getIncomingBlock(*U)->getTerminator()->getIterator();
                else
                    IP = UI->getIterator();
                // Clone only the chain feeding this use (cached per use in
                // VMap); cloning the whole region spine at every use is
                // quadratic in the interface size.
                ValueToValueMapTy VMap;
                SmallVector<Instruction *, RematSpineLimit> Chain;
                SmallVector<Instruction *, RematSpineLimit> Work{I};
                SmallPtrSet<Instruction *, 16> Seen{I};
                while (!Work.empty()) {
                    Instruction *SI = Work.pop_back_val();
                    Chain.push_back(SI);
                    for (Value *Op : SI->operands()) {
                        auto *OpI = dyn_cast<Instruction>(Op);
                        if (OpI && SiteSet.count(OpI) && Seen.insert(OpI).second)
                            Work.push_back(OpI);
                    }
                }
                // Operands-first: SiteSpine is already in that order.
                for (Instruction *SI : SiteSpine) {
                    if (!Seen.count(SI))
                        continue;
                    Instruction *Clone = SI->clone();
                    Clone->setName(SI->getName() + ".remat");
                    Clone->insertBefore(IP);
                    for (Use &COp : Clone->operands()) {
                        auto *OpI = dyn_cast<Instruction>(COp.get());
                        if (!OpI)
                            continue;
                        if (auto It = Slot.find(OpI); It != Slot.end()) {
                            auto *L = new LoadInst(OpI->getType(), It->second,
                                                   OpI->getName() + ".reload",
                                                   Clone->getIterator());
                            COp.set(L);
                        }
                    }
                    RemapInstruction(Clone, VMap,
                                     RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
                    VMap[SI] = Clone;
                }
                U->set(VMap[I]);
            }
        }
    }
    RematSiteUs += rus(R3, rnow());
    return true;
}

// Reduce an oversized region interface by passing values through two stack
// aggregates instead of individual arguments: tracked (AS10) values go through
// an array-of-AS10 alloca (which the caller's LateLowerGCFrame turns into GC
// frame slots, so every intermediate state is properly rooted; the frame is
// zero-initialized at push, so slots written only inside the callee scan as
// null until then) and untracked values through an ordinary struct alloca.
// Derived and Mixed inputs remain direct arguments, as do uses not dominated
// by the boundary (e.g. on cold exit paths) which stay ordinary CodeExtractor
// outputs.
static void spillInterface(Function &F, Region &R, const DominatorTree &DT,
                           const SmallPtrSetImpl<BasicBlock *> &Owned,
                           const SetVector<Value *> &Inputs,
                           const SetVector<Value *> &Outputs) JL_NOTSAFEPOINT
{
    BasicBlock *Entry = R.Blocks[0];
    BasicBlock *Boundary = R.Boundary;
    // Input fills go in the region's preheader, which flows unconditionally
    // into the region. (For loop regions the fills run once, but the reloads
    // inside the region re-read the slots on every iteration.)
    BasicBlock *Pred = regionPreheader(R, Owned);

    SmallVector<Value *, 16> TIn, UIn;
    SmallVector<Instruction *, 16> TOut, UOut;
    if (Pred && !SplitNoInputSpill) {
        for (Value *V : Inputs) {
            switch (classifyType(V->getType())) {
            case ValKind::Tracked:
                TIn.push_back(V);
                break;
            case ValKind::Untracked:
                if (V->getType()->isFirstClassType() && V->getType()->isSized())
                    UIn.push_back(V);
                break;
            default:
                break;
            }
        }
    }
    if (Boundary && !SplitNoOutputSpill) {
        for (Value *V : Outputs) {
            auto *I = cast<Instruction>(V);
            switch (classifyType(I->getType())) {
            case ValKind::Tracked:
                TOut.push_back(I);
                break;
            case ValKind::Untracked:
                if (I->getType()->isFirstClassType() && I->getType()->isSized())
                    UOut.push_back(I);
                break;
            default:
                break;
            }
        }
    }
    if (TIn.empty() && UIn.empty() && TOut.empty() && UOut.empty())
        return;
    static int SpillCount = 0;
    if (SplitSpillMax >= 0 && SpillCount >= SplitSpillMax)
        return;
    SpillCount++;
    if (SplitDebug)
        errs() << "julia-function-splitting: spill #" << SpillCount << " at "
               << Entry->getName() << " TIn=" << TIn.size() << " UIn=" << UIn.size()
               << " TOut=" << TOut.size() << " UOut=" << UOut.size() << "\n";
    ++RegionsSpilled;

    LLVMContext &Ctx = F.getContext();
    Type *T_prjlvalue = PointerType::get(Ctx, AddressSpace::Tracked);
    IRBuilder<> EB(&F.getEntryBlock(), F.getEntryBlock().begin());
    AllocaInst *TSpill = nullptr;
    unsigned NT = TIn.size() + TOut.size();
    if (NT) {
        TSpill = EB.CreateAlloca(T_prjlvalue, EB.getInt32(NT), "gcspill");
        TSpill->setAlignment(Align(sizeof(void *)));
    }
    StructType *UTy = nullptr;
    AllocaInst *USpill = nullptr;
    if (!UIn.empty() || !UOut.empty()) {
        SmallVector<Type *, 16> Elts;
        for (Value *V : UIn)
            Elts.push_back(V->getType());
        for (Instruction *I : UOut)
            Elts.push_back(I->getType());
        UTy = StructType::get(Ctx, Elts);
        USpill = EB.CreateAlloca(UTy, nullptr, "spill");
    }

    IRBuilder<> RegionFront(Entry, Entry->getFirstInsertionPt());
    unsigned TSlot = 0, USlot = 0;
    if (!TIn.empty() || !UIn.empty()) {
        IRBuilder<> FB(Pred->getTerminator());
        // Map each spilled input to its in-region reload, then rewrite all
        // in-region operands in one sweep: iterating uses of the inputs
        // directly is quadratic for high-fanout values (pgcstack, task,
        // closure arguments) that hundreds of regions each spill.
        DenseMap<Value *, Value *> InputReload;
        for (Value *V : TIn) {
            FB.CreateAlignedStore(
                V, FB.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpill, TSlot),
                Align(sizeof(void *)));
            auto *Reload = RegionFront.CreateAlignedLoad(
                T_prjlvalue,
                RegionFront.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpill, TSlot),
                Align(sizeof(void *)), V->getName() + ".in");
            InputReload[V] = Reload;
            TSlot++;
        }
        for (Value *V : UIn) {
            FB.CreateStore(V, FB.CreateStructGEP(UTy, USpill, USlot));
            auto *Reload = RegionFront.CreateLoad(
                V->getType(), RegionFront.CreateStructGEP(UTy, USpill, USlot),
                V->getName() + ".in");
            InputReload[V] = Reload;
            USlot++;
        }
        SmallPtrSet<Value *, 16> Reloads;
        for (auto &KV : InputReload)
            Reloads.insert(KV.second);
        for (BasicBlock *BB : R.Blocks) {
            for (Instruction &I : *BB) {
                if (Reloads.count(&I))
                    continue;
                if (auto *PN = dyn_cast<PHINode>(&I)) {
                    for (unsigned i = 0, e = PN->getNumIncomingValues(); i < e; i++) {
                        if (!R.Set.count(PN->getIncomingBlock(i)))
                            continue; // that use is located outside the region
                        if (auto It = InputReload.find(PN->getIncomingValue(i));
                            It != InputReload.end())
                            PN->setIncomingValue(i, It->second);
                    }
                    continue;
                }
                for (Use &U : I.operands())
                    if (auto It = InputReload.find(U.get()); It != InputReload.end())
                        U.set(It->second);
            }
        }
    }
    if (!TOut.empty() || !UOut.empty()) {
        // Store each output right after its definition (the value stays live
        // in SSA until then, so the callee's own GC lowering keeps it rooted;
        // the slot then always holds the most recent def). Each external use
        // re-reads the slot right where it needs it: unlike a reload placed at
        // the boundary, this stays correct when the boundary sits on a cycle
        // and can execute before the region has run.
        auto storePoint = [](Instruction *I) JL_NOTSAFEPOINT -> BasicBlock::iterator {
            if (isa<PHINode>(I))
                return I->getParent()->getFirstInsertionPt();
            return std::next(I->getIterator());
        };
        auto rewriteOutputUses = [&](Instruction *I, auto MakeGEP) JL_NOTSAFEPOINT {
            SmallVector<Use *, 8> ExtUses;
            for (Use &U : I->uses())
                if (!R.Set.count(useBlock(U)))
                    ExtUses.push_back(&U);
            for (Use *U : ExtUses) {
                auto *UI = cast<Instruction>(U->getUser());
                BasicBlock::iterator IP;
                if (auto *PN = dyn_cast<PHINode>(UI))
                    IP = PN->getIncomingBlock(*U)->getTerminator()->getIterator();
                else
                    IP = UI->getIterator();
                // Materialize the slot address at the use site (a single GEP
                // per use; entry-block GEPs would accumulate O(outputs) code
                // in the outermost caller).
                Value *G = MakeGEP(IP);
                auto *L = new LoadInst(I->getType(), G, I->getName() + ".out", IP);
                L->setAlignment(Align(sizeof(void *)));
                U->set(L);
            }
        };
        for (Instruction *I : TOut) {
            IRBuilder<> SB(I->getParent(), storePoint(I));
            SB.CreateAlignedStore(
                I, SB.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpill, TSlot),
                Align(sizeof(void *)));
            unsigned Slot = TSlot;
            rewriteOutputUses(I, [&, Slot](BasicBlock::iterator IP) JL_NOTSAFEPOINT -> Value * {
                IRBuilder<> B(IP->getParent(), IP);
                return B.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpill, Slot);
            });
            TSlot++;
        }
        for (Instruction *I : UOut) {
            IRBuilder<> SB(I->getParent(), storePoint(I));
            SB.CreateStore(I, SB.CreateStructGEP(UTy, USpill, USlot));
            unsigned Slot = USlot;
            rewriteOutputUses(I, [&, Slot](BasicBlock::iterator IP) JL_NOTSAFEPOINT -> Value * {
                IRBuilder<> B(IP->getParent(), IP);
                return B.CreateStructGEP(UTy, USpill, Slot);
            });
            USlot++;
        }
    }
}

// Sub-stage accumulators (diagnostics; printed under -julia-split-debug).
static int64_t PrepRematMs, PrepCEMs, PrepIOMs, PrepSpillMs;
// Region-growth outcome counters (reset per function; printed under
// -julia-split-time). "clamp" cuts and growth failures mean the realized
// region sizes diverge from the requested target — never silently.
static int64_t GrowCutTarget, GrowCutClamp, GrowFailBlocks, GrowFailSize, GrowFailNoAdd;
// Interface statistics across a function's extractions (reset per function).
static int64_t IfaceIn, IfaceOut, IfaceInMax, IfaceOutMax, IfaceExits, IfaceCalls;

// CodeExtractor rewrites a region's uses of each input by scanning the
// input's *entire* use list, which is quadratic for high-fanout values that
// almost every region reads (pgcstack, the task pointer, array arguments,
// hoisted data pointers). Give each region a private low-fanout proxy: an
// identity bitcast of the value in the region's preheader. LateLowerGCFrame's
// FindBaseValue looks through bitcasts (so tracked and derived values keep
// rooting to their real base) and InstCombine folds each one away in O(1)
// after extraction. (A `freeze` proxy is unsuitable: InstCombine's
// freezeOtherUses canonicalization rescans the operand's whole use list per
// freeze, which is exactly the quadratic behavior being avoided here.)
static void localizeRegionInputs(Region &R,
                                 const SmallPtrSetImpl<BasicBlock *> &Owned,
                                 DenseMap<Value *, bool> &HighFanout) JL_NOTSAFEPOINT
{
    BasicBlock *Pred = regionPreheader(R, Owned);
    if (!Pred)
        return;
    auto isHighFanout = [&](Value *V) JL_NOTSAFEPOINT {
        auto It = HighFanout.find(V);
        if (It != HighFanout.end())
            return It->second;
        return HighFanout[V] = V->hasNUsesOrMore(48);
    };
    DenseMap<Value *, Value *> Local;
    IRBuilder<> PB(Pred->getTerminator());
    auto proxyFor = [&](Value *V) JL_NOTSAFEPOINT -> Value * {
        auto It = Local.find(V);
        if (It != Local.end())
            return It->second;
        Instruction *Proxy = new BitCastInst(V, V->getType(), V->getName() + ".loc");
        PB.Insert(Proxy);
        return Local[V] = Proxy;
    };
    auto wants = [&](Value *V) JL_NOTSAFEPOINT {
        if (isa<Constant>(V) || isa<BasicBlock>(V) || isa<MetadataAsValue>(V))
            return false;
        if (!isa<Argument>(V) && !isa<Instruction>(V))
            return false;
        if (auto *I = dyn_cast<Instruction>(V); I && R.Set.count(I->getParent()))
            return false;
        Type *T = V->getType();
        if (!T->isFirstClassType() || T->isAggregateType() || T->isTokenTy())
            return false; // identity bitcast must be valid on the type
        if (T->isPtrOrPtrVectorTy() &&
            T->getPointerAddressSpace() == AddressSpace::CalleeRooted)
            return false;
        return isHighFanout(V);
    };
    for (BasicBlock *BB : R.Blocks) {
        for (Instruction &I : *BB) {
            if (auto *PN = dyn_cast<PHINode>(&I)) {
                for (unsigned i = 0, e = PN->getNumIncomingValues(); i < e; i++) {
                    if (!R.Set.count(PN->getIncomingBlock(i)))
                        continue;
                    Value *V = PN->getIncomingValue(i);
                    if (wants(V))
                        PN->setIncomingValue(i, proxyFor(V));
                }
                continue;
            }
            for (Use &U : I.operands())
                if (wants(U.get()))
                    U.set(proxyFor(U.get()));
        }
    }
}

// Legality check + interface preparation for one region.
static bool prepareRegion(Function &F, Region &R, const DominatorTree &DT,
                          const SmallPtrSetImpl<BasicBlock *> &Owned,
                          DenseMap<Value *, bool> &HighFanout,
                          const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    localizeRegionInputs(R, Owned, HighFanout);
    auto now = []() JL_NOTSAFEPOINT { return std::chrono::steady_clock::now(); };
    auto msc = [](auto a, auto b) JL_NOTSAFEPOINT {
        return std::chrono::duration_cast<std::chrono::microseconds>(b - a).count();
    };
    auto P0 = now();
    bool RematOK = rematerializeDerivedOutputs(F, R, DT, Owned, ctx);
    auto P1 = now();
    PrepRematMs += msc(P0, P1);
    if (!RematOK) {
        if (SplitDebug)
            errs() << "julia-function-splitting: reject (remat) at "
                   << R.Blocks[0]->getName() << "\n";
        return false;
    }
    auto P2 = now();
    CodeExtractor CE(R.Blocks, /*DT*/ nullptr, /*AggregateArgs*/ false,
                     /*BFI*/ nullptr, /*BPI*/ nullptr, /*AC*/ nullptr,
                     /*AllowVarArgs*/ false, /*AllowAlloca*/ true);
    bool Eligible = CE.isEligible();
    auto P3 = now();
    PrepCEMs += msc(P2, P3);
    if (!Eligible) {
        if (SplitDebug)
            errs() << "julia-function-splitting: reject (eligibility) at "
                   << R.Blocks[0]->getName() << "\n";
        return false;
    }
    SetVector<Value *> Inputs, Outputs;
    CE.findInputsOutputs(Inputs, Outputs, {});
    auto P4 = now();
    PrepIOMs += msc(P3, P4);
    for (Value *V : Inputs) {
        ValKind K = classifyType(V->getType());
        if (K == ValKind::CalleeRooted || K == ValKind::TokenLike) {
            if (SplitDebug)
                errs() << "julia-function-splitting: reject (input kind) at "
                       << R.Blocks[0]->getName() << "\n";
            return false;
        }
    }
    for (Value *V : Outputs) {
        ValKind K = classifyType(V->getType());
        if (K != ValKind::Tracked && K != ValKind::Untracked) {
            if (SplitDebug)
                errs() << "julia-function-splitting: reject (output kind) at "
                       << R.Blocks[0]->getName() << "\n";
            return false;
        }
    }
    auto P5 = now();
    if (Inputs.size() + Outputs.size() > SplitDirectArgLimit) {
        spillInterface(F, R, DT, Owned, Inputs, Outputs);
    }
    else if (SplitOutputSpillMin && Outputs.size() >= SplitOutputSpillMin) {
        // Narrow interface, but still route the outputs through the aggregate:
        // CodeExtractor's fallback is one scalar output alloca per value, i.e.
        // one pointer argument and one isolated stack slot each, which defeats
        // vectorized marshalling and bloats the call frame. Inputs stay direct
        // (they ride in registers).
        SetVector<Value *> NoInputs;
        spillInterface(F, R, DT, Owned, NoInputs, Outputs);
    }
    PrepSpillMs += msc(P5, now());
    return true;
}

// Conservatively determine whether an outlined function may reach a safepoint
// (and hence needs a pgcstack for its GC frame). Over-approximation only
// wastes one TLS load.
static bool mayReachSafepoint(Function &F, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    for (Instruction &I : instructions(F)) {
        auto *CI = dyn_cast<CallBase>(&I);
        if (!CI || isa<IntrinsicInst>(CI))
            continue;
        Function *Callee = CI->getCalledFunction();
        if (Callee && (Callee == ctx.gc_loaded_func || Callee == ctx.typeof_func ||
                       Callee == ctx.write_barrier_func || Callee == ctx.pointer_from_objref_func ||
                       Callee == ctx.gcroot_flush_func || Callee == ctx.blackbox_func))
            continue;
        return true;
    }
    return false;
}

static Function *extractRegion(Function &F, Region &R, const JuliaPassContext &ctx,
                               const CodeExtractorAnalysisCache &CEAC) JL_NOTSAFEPOINT
{
    Module *M = F.getParent();
    LLVMContext &Ctx = F.getContext();
    Value *CallerPG = ctx.getPGCstack(F);
    CodeExtractor CE(R.Blocks, /*DT*/ nullptr, /*AggregateArgs*/ false,
                     /*BFI*/ nullptr, /*BPI*/ nullptr, /*AC*/ nullptr,
                     /*AllowVarArgs*/ false, /*AllowAlloca*/ true,
                     /*AllocationBlock*/ nullptr, /*Suffix*/ "julia_split");
    if (!CE.isEligible())
        return nullptr;
    SetVector<Value *> Inputs, Outputs;
    Function *NewF = CE.extractCodeRegion(CEAC, Inputs, Outputs);
    if (!NewF)
        return nullptr;
    ++RegionsExtracted;
    IfaceIn += Inputs.size();
    IfaceOut += Outputs.size();
    IfaceInMax = std::max<int64_t>(IfaceInMax, Inputs.size());
    IfaceOutMax = std::max<int64_t>(IfaceOutMax, Outputs.size());

    // Sunk allocas (see sinkEntryAllocas) must be static again: hoist any
    // alloca in the extracted body to the new function's entry block.
    {
        BasicBlock &NE = NewF->getEntryBlock();
        SmallVector<AllocaInst *, 16> ToHoist;
        for (BasicBlock &BB : *NewF)
            if (&BB != &NE)
                for (Instruction &I : BB)
                    if (auto *AI = dyn_cast<AllocaInst>(&I))
                        ToHoist.push_back(AI);
        for (AllocaInst *AI : ToHoist)
            AI->moveBefore(NE.getFirstInsertionPt());
    }

    NewF->setLinkage(GlobalValue::InternalLinkage);
    NewF->removeFnAttr(Attribute::AlwaysInline);
    NewF->addFnAttr(Attribute::NoInline);
    for (StringRef AN : {"target-cpu", "target-features", "tune-cpu", "frame-pointer"})
        if (!NewF->hasFnAttribute(AN) && F.hasFnAttribute(AN))
            NewF->addFnAttr(F.getFnAttribute(AN));

    CallBase *CS = nullptr;
    for (User *U : NewF->users()) {
        if (auto *CI = dyn_cast<CallBase>(U); CI && CI->getCalledFunction() == NewF) {
            CS = CI;
            break;
        }
    }
    if (CS) {
        IfaceCalls++;
        IfaceExits += CS->getParent()->getTerminator()->getNumSuccessors();
    }
    // Give the callee a pgcstack: reuse the caller's if it happened to be a
    // region input, otherwise materialize julia.get_pgcstack in the entry
    // block (both forms are recognized by LateLowerGCFrame).
    bool HavePG = false;
    if (CS && CallerPG) {
        for (unsigned i = 0; i < CS->arg_size(); i++) {
            if (CS->getArgOperand(i) == CallerPG) {
                NewF->addParamAttr(i, Attribute::get(Ctx, "gcstack"));
                HavePG = true;
                break;
            }
        }
    }
    if (!HavePG && mayReachSafepoint(*NewF, ctx)) {
        Function *Getter = M->getFunction("julia.get_pgcstack");
        if (!Getter)
            Getter = Function::Create(FunctionType::get(PointerType::get(Ctx, 0), false),
                                      GlobalValue::ExternalLinkage, "julia.get_pgcstack", M);
        IRBuilder<> EB(&NewF->getEntryBlock(), NewF->getEntryBlock().begin());
        EB.CreateCall(Getter, {}, "pgcstack");
    }
    LLVM_DEBUG(dbgs() << "julia-function-splitting: extracted " << NewF->getName()
                      << " (" << NewF->getInstructionCount() << " instructions) from "
                      << F.getName() << "\n");
    return NewF;
}

// Codegen reuses each GC root buffer (an all-tracked stack array filled
// right before every call that reads it) across many callsites, which after
// splitting spans many regions: the shared alloca then pins the caller entry
// (growing with function size) and threads through every region interface.
// When every read of a buffer is self-sufficient — all of its slots are
// stored earlier in the read's own block, so no read anywhere observes
// values written by another region — each region can use a private copy
// instead. All-or-nothing per buffer: privatizing only some regions would
// starve the remaining readers of the shared one.
static void privatizeRootBuffers(Function &F, std::vector<Region> &Leaves) JL_NOTSAFEPOINT
{
    const DataLayout &DL = F.getParent()->getDataLayout();
    DenseMap<BasicBlock *, Region *> RegionOf;
    for (Region &R : Leaves)
        for (BasicBlock *B : R.Blocks)
            RegionOf[B] = &R;
    BasicBlock &Entry = F.getEntryBlock();
    SmallVector<AllocaInst *, 64> Allocas;
    for (Instruction &I : Entry)
        if (auto *AI = dyn_cast<AllocaInst>(&I))
            if (AI->isStaticAlloca()) {
                auto tracked = CountTrackedPointers(AI->getAllocatedType());
                if (tracked.count && tracked.all && !tracked.derived)
                    Allocas.push_back(AI);
            }
    unsigned Privatized = 0, RejectedShape = 0, RejectedCoverage = 0;
    for (AllocaInst *AI : Allocas) {
        uint64_t Bytes = DL.getTypeAllocSize(AI->getAllocatedType()) *
                         cast<ConstantInt>(AI->getArraySize())->getZExtValue();
        uint64_t PtrBytes = DL.getPointerSize();
        if (Bytes == 0 || Bytes % PtrBytes)
            continue;
        int64_t NumSlots = (int64_t)(Bytes / PtrBytes);
        // Walk the address chain, recording constant byte offsets.
        DenseMap<Value *, int64_t> Off;
        Off[AI] = 0;
        SmallVector<Instruction *, 32> Chain; // discovery (def-before-use) order
        SmallVector<Value *, 32> Work{AI};
        SmallVector<StoreInst *, 32> Stores;
        SmallVector<MemSetInst *, 8> Zeros;
        SmallVector<Instruction *, 32> Reads;
        bool Reject = false;
        while (!Work.empty() && !Reject) {
            Value *A = Work.pop_back_val();
            for (Use &UU : A->uses()) {
                auto *UI = dyn_cast<Instruction>(UU.getUser());
                if (!UI) {
                    Reject = true;
                    break;
                }
                if (auto *G = dyn_cast<GetElementPtrInst>(UI)) {
                    APInt O(DL.getIndexSizeInBits(G->getPointerAddressSpace()), 0);
                    if (G->getPointerOperand() != A ||
                        !G->accumulateConstantOffset(DL, O) || Chain.size() >= 64) {
                        Reject = true;
                        break;
                    }
                    if (Off.insert({G, Off[A] + O.getSExtValue()}).second) {
                        Chain.push_back(G);
                        Work.push_back(G);
                    }
                }
                else if (isa<BitCastInst>(UI) || isa<AddrSpaceCastInst>(UI)) {
                    if (Chain.size() >= 64) {
                        Reject = true;
                        break;
                    }
                    if (Off.insert({UI, Off[A]}).second) {
                        Chain.push_back(UI);
                        Work.push_back(UI);
                    }
                }
                else if (auto *SI = dyn_cast<StoreInst>(UI)) {
                    if (SI->getValueOperand() == A) {
                        Reject = true; // address escapes into memory
                        break;
                    }
                    Stores.push_back(SI);
                }
                else if (auto *MS = dyn_cast<MemSetInst>(UI)) {
                    // Zero-init in memset form: a covering write, not a read.
                    if (MS->getRawDest() != A || !isa<ConstantInt>(MS->getLength()) ||
                        !isa<ConstantInt>(MS->getValue()) ||
                        !cast<ConstantInt>(MS->getValue())->isZero()) {
                        Reject = true;
                        break;
                    }
                    Zeros.push_back(MS);
                }
                else if (auto *CB = dyn_cast<CallBase>(UI)) {
                    if (!CB->isArgOperand(&UU) ||
                        !CB->doesNotCapture(CB->getArgOperandNo(&UU))) {
                        Reject = true;
                        break;
                    }
                    Reads.push_back(CB);
                }
                else if (isa<LoadInst>(UI)) {
                    Reads.push_back(UI);
                }
                else {
                    Reject = true;
                    break;
                }
            }
        }
        if (Reject) {
            RejectedShape++;
            continue;
        }
        if (Reads.empty())
            continue; // store-only; nothing to gain
        // Every read must find stores covering all slots earlier in its own
        // block; then no read depends on another region's writes.
        bool Covered = true;
        for (Instruction *Rd : Reads) {
            SmallVector<bool, 8> Seen((unsigned)NumSlots, false);
            int64_t Left = NumSlots;
            unsigned Steps = 0;
            // Walk backward, following unique predecessor edges within the
            // read's own region (covering stores must be rewritten together
            // with the read, so they may not come from another region).
            Region *ReadRegion = RegionOf.lookup(Rd->getParent());
            BasicBlock *BB = Rd->getParent();
            Instruction *Cur = Rd->getPrevNode();
            while (Steps < 256 && Left) {
                if (!Cur) {
                    BasicBlock *Pred = BB->getUniquePredecessor();
                    if (!Pred || RegionOf.lookup(Pred) != ReadRegion)
                        break;
                    BB = Pred;
                    Cur = BB->empty() ? nullptr : &BB->back();
                    continue;
                }
                if (auto *SI = dyn_cast<StoreInst>(Cur)) {
                    auto It = Off.find(SI->getPointerOperand());
                    if (It != Off.end()) {
                        int64_t Slot = It->second / (int64_t)PtrBytes;
                        if (Slot >= 0 && Slot < NumSlots && !Seen[(unsigned)Slot]) {
                            Seen[(unsigned)Slot] = true;
                            Left--;
                        }
                    }
                }
                else if (auto *MS = dyn_cast<MemSetInst>(Cur)) {
                    auto It = Off.find(MS->getRawDest());
                    if (It != Off.end() && isa<ConstantInt>(MS->getLength())) {
                        int64_t Lo = It->second / (int64_t)PtrBytes;
                        int64_t Hi = (It->second +
                                      (int64_t)cast<ConstantInt>(MS->getLength())->getSExtValue()) /
                                     (int64_t)PtrBytes;
                        for (int64_t Slot = std::max<int64_t>(Lo, 0);
                             Slot < std::min(Hi, NumSlots); Slot++) {
                            if (!Seen[(unsigned)Slot]) {
                                Seen[(unsigned)Slot] = true;
                                Left--;
                            }
                        }
                    }
                }
                Cur = Cur->getPrevNode();
                Steps++;
            }
            if (Left) {
                if (SplitDebug)
                    errs() << "julia-function-splitting: uncovered read (slots left "
                           << Left << "/" << NumSlots << "): " << *Rd << "\n";
                Covered = false;
                break;
            }
        }
        if (!Covered) {
            RejectedCoverage++;
            continue;
        }
        // Rewrite each region's uses to a region-private copy with a cloned
        // address chain; caller-resident uses keep the original.
        DenseMap<Region *, DenseMap<Value *, Value *>> Priv;
        auto privFor = [&](Region *R, Value *A, auto &&Self) JL_NOTSAFEPOINT -> Value * {
            auto &M = Priv[R];
            auto It = M.find(A);
            if (It != M.end())
                return It->second;
            Instruction *C;
            if (A == AI) {
                auto *NA = new AllocaInst(AI->getAllocatedType(),
                                          AI->getAddressSpace(), AI->getArraySize(),
                                          AI->getAlign(), AI->getName() + ".priv");
                NA->insertBefore(R->Blocks[0]->getFirstInsertionPt());
                C = NA;
            }
            else {
                auto *Orig = cast<Instruction>(A);
                unsigned PtrIdx = isa<GetElementPtrInst>(Orig)
                                      ? GetElementPtrInst::getPointerOperandIndex()
                                      : 0u;
                Value *Base = Self(R, Orig->getOperand(PtrIdx), Self);
                C = Orig->clone();
                C->setName(Orig->getName() + ".priv");
                C->setOperand(PtrIdx, Base);
                C->insertBefore(R->Blocks[0]->getFirstInsertionPt());
                // Address computations only; no metadata worth remapping.
            }
            M[A] = C;
            return C;
        };
        SmallVector<Instruction *, 32> Users;
        Users.append(Stores.begin(), Stores.end());
        Users.append(Zeros.begin(), Zeros.end());
        Users.append(Reads.begin(), Reads.end());
        for (Instruction *U : Users) {
            Region *R = RegionOf.lookup(U->getParent());
            if (!R)
                continue;
            for (Use &Op : U->operands())
                if (Off.count(Op.get()))
                    Op.set(privFor(R, Op.get(), privFor));
        }
        Privatized++;
        // Now-dead pieces of the shared chain (and the alloca itself, if all
        // its clusters moved) are cleaned up by sinkEntryAllocas below.
    }
    if (SplitDebug || SplitTime)
        errs() << "julia-function-splitting: privatized " << Privatized << "/"
               << Allocas.size() << " tracked buffers (rejected: "
               << RejectedShape << " shape, " << RejectedCoverage
               << " coverage; rest store-only/odd-size)\n";
}

// The entry block of a huge codegen'd function holds thousands of per-op GC
// root buffers ([N x ptr addrspace(10)] allocas) with paired null-init
// stores; that block is pinned and would otherwise remain the dominant
// residue in the caller. Two reductions: the null-init stores are redundant
// (LateLowerGCFrame registers every all-tracked static alloca as GC frame
// slots and the frame is zeroed when pushed), and an alloca whose uses all
// lie inside a single region can move into it (no other region can observe
// the slot's contents, so a fresh per-call slot is equivalent); extraction
// later hoists it into the new function's entry so it stays static.
static void sinkEntryAllocas(Function &F, std::vector<Region> &Leaves) JL_NOTSAFEPOINT
{
    DenseMap<BasicBlock *, Region *> RegionOf;
    for (Region &R : Leaves)
        for (BasicBlock *B : R.Blocks)
            RegionOf[B] = &R;
    BasicBlock &Entry = F.getEntryBlock();
    SmallVector<AllocaInst *, 64> Allocas;
    for (Instruction &I : Entry)
        if (auto *AI = dyn_cast<AllocaInst>(&I))
            if (AI->isStaticAlloca())
                Allocas.push_back(AI);
    for (AllocaInst *AI : Allocas) {
        auto tracked = CountTrackedPointers(AI->getAllocatedType());
        bool AllTracked = tracked.count && tracked.all && !tracked.derived;
        // Transitive address producers rooted at the alloca.
        SmallVector<Instruction *, 32> Addrs{AI};
        SmallPtrSet<Value *, 32> AddrSet{AI};
        SmallVector<Instruction *, 32> Users;
        bool Bail = false;
        for (unsigned i = 0; i < Addrs.size() && !Bail; i++) {
            for (User *U : Addrs[i]->users()) {
                auto *UI = dyn_cast<Instruction>(U);
                if (!UI) {
                    Bail = true;
                    break;
                }
                if (isa<GetElementPtrInst>(UI) || isa<BitCastInst>(UI) ||
                    isa<AddrSpaceCastInst>(UI)) {
                    if (Addrs.size() >= 64) {
                        Bail = true;
                        break;
                    }
                    if (AddrSet.insert(UI).second)
                        Addrs.push_back(UI);
                }
                else {
                    Users.push_back(UI);
                }
            }
        }
        if (Bail)
            continue;
        if (AllTracked) {
            // Null-init stores in the entry are covered by the GC frame memset.
            SmallVector<Instruction *, 8> Dead;
            for (Instruction *U : Users) {
                auto *SI = dyn_cast<StoreInst>(U);
                if (SI && SI->getParent() == &Entry &&
                    AddrSet.count(SI->getPointerOperand()) &&
                    isa<Constant>(SI->getValueOperand()) &&
                    cast<Constant>(SI->getValueOperand())->isNullValue())
                    Dead.push_back(SI);
            }
            for (Instruction *SI : Dead) {
                llvm::erase(Users, SI);
                SI->eraseFromParent();
            }
        }
        if (Users.empty()) {
            // Fully dead (e.g. a privatized buffer): erase the chain.
            for (Instruction *A : llvm::reverse(Addrs))
                if (A->use_empty())
                    A->eraseFromParent();
            continue;
        }
        Region *Owner = nullptr;
        bool Escapes = false;
        for (Instruction *U : Users) {
            Region *R = RegionOf.lookup(U->getParent());
            if (!R || (Owner && R != Owner)) {
                Escapes = true;
                break;
            }
            Owner = R;
        }
        if (Escapes || !Owner)
            continue;
        // Move the alloca (and its entry-resident address computations, in
        // order) to the owning region's entry; erase the now-dead ones.
        BasicBlock::iterator IP = Owner->Blocks[0]->getFirstInsertionPt();
        for (Instruction *A : Addrs) {
            if (A->getParent() != &Entry)
                continue;
            if (A->use_empty() && A != AI) {
                A->eraseFromParent();
                continue;
            }
            A->moveBefore(IP);
        }
    }
}

// A node of the hierarchical decomposition: a region plus the child regions
// nested inside it (empty for leaves). Parents are extracted first; children
// are then extracted from within the parent's new function, so every level's
// interface glue lands in its parent rather than the outermost caller.
struct HNode {
    Region R;
    std::vector<HNode> Kids;
};

// Grow a parent region by interval growth over the quotient graph: existing
// nodes are atomic (added whole, via their entry) and caller-resident glue
// blocks are added individually, under the same rules as leaf formation. The
// resulting parent is single-entry with a unique non-cold continue target.
static bool growParent(BasicBlock *Entry, unsigned Target, BlockInfoCache &Info,
                       const DenseMap<BasicBlock *, HNode *> &AtomOf,
                       const SmallPtrSetImpl<BasicBlock *> &Assigned,
                       const DenseMap<BasicBlock *, unsigned> &RPOIndex,
                       Region &PR, SmallVectorImpl<HNode *> &Members) JL_NOTSAFEPOINT
{
    unsigned MinSize = std::max(32u, Target / 4);
    unsigned MaxSize = 4 * Target;
    unsigned Insts = 0;
    unsigned Pending = 0; // outside edges into non-entry members (see growRegion)
    DenseMap<BasicBlock *, std::pair<unsigned, unsigned>> Fringe;
    SmallVector<BasicBlock *, 16> NewBlocks;
    auto addAtom = [&](BasicBlock *B) JL_NOTSAFEPOINT {
        NewBlocks.clear();
        auto It = AtomOf.find(B);
        if (It != AtomOf.end()) {
            HNode *N = It->second;
            NewBlocks.append(N->R.Blocks.begin(), N->R.Blocks.end());
            Insts += N->R.Insts;
            Members.push_back(N);
        }
        else {
            NewBlocks.push_back(B);
            Insts += Info.get(B).first;
        }
        for (BasicBlock *NB : NewBlocks) {
            PR.Set.insert(NB);
            PR.Blocks.push_back(NB);
            Fringe.erase(NB);
        }
        for (BasicBlock *NB : NewBlocks) {
            if (NB != Entry)
                for (BasicBlock *P : predecessors(NB))
                    if (!PR.Set.count(P))
                        Pending++;
            for (BasicBlock *S : successors(NB)) {
                if (PR.Set.count(S)) {
                    bool InNew = llvm::is_contained(NewBlocks, S);
                    if (S != Entry && !InNew)
                        Pending--;
                    continue;
                }
                auto &FE = Fringe[S];
                if (FE.second == 0)
                    FE.second = std::distance(pred_begin(S), pred_end(S));
                FE.first++;
            }
        }
    };
    // Seed.
    {
        auto It = AtomOf.find(Entry);
        if (It == AtomOf.end()) {
            auto [ESize, EPinned] = Info.get(Entry);
            if (EPinned || isa<ReturnInst>(Entry->getTerminator()))
                return false;
        }
        else if (It->second->R.Blocks[0] != Entry) {
            return false;
        }
        addAtom(Entry);
        // Intra-atom edges into the atom's own entry are loop backedges of a
        // fully-contained loop, not debt; addAtom already skips edges whose
        // source is inside. Fix Blocks[0] to be the entry.
        auto BIt = llvm::find(PR.Blocks, Entry);
        std::swap(*PR.Blocks.begin(), *BIt);
    }
    while (true) {
        BasicBlock *Add = nullptr;
        unsigned AddIdx = ~0u;
        BasicBlock *Cand = nullptr;
        unsigned CandIdx = ~0u;
        bool CandFull = false;
        for (auto &FE : Fringe) {
            BasicBlock *S = FE.first;
            bool Full = FE.second.first == FE.second.second;
            if (Assigned.count(S))
                continue;
            if (!Info.isCold(S)) {
                unsigned Idx = RPOIndex.lookup(S);
                if (!Cand || (Full && !CandFull) ||
                    (Full == CandFull && Idx < CandIdx)) {
                    Cand = S;
                    CandIdx = Idx;
                    CandFull = Full;
                }
            }
            if (!Full)
                continue;
            auto It = AtomOf.find(S);
            if (It != AtomOf.end()) {
                if (It->second->R.Blocks[0] != S)
                    continue; // interior block of a node; only enter via entry
            }
            else {
                auto [SSize, SPinned] = Info.get(S);
                if (SPinned || isa<ReturnInst>(S->getTerminator()))
                    continue;
            }
            unsigned Idx = RPOIndex.lookup(S);
            if (!Add || Idx < AddIdx) {
                Add = S;
                AddIdx = Idx;
            }
        }
        bool CanCut = Cand != nullptr && Pending == 0;
        // Cap direct children as well as instructions: when leftovers from a
        // lower level get pooled here, a parent could otherwise absorb
        // hundreds of children whose interface glue it permanently retains.
        bool Enough = Insts >= Target || Members.size() >= 2 * SplitGroupSize;
        if (CanCut && Enough && Members.size() >= 2) {
            PR.Boundary = Cand;
            PR.BoundaryDominated = CandFull;
            PR.Insts = Insts;
            return true;
        }
        if (!Add || Insts >= MaxSize || Members.size() >= 4 * SplitGroupSize) {
            if (CanCut && Insts >= MinSize && Members.size() >= 2) {
                PR.Boundary = Cand;
                PR.BoundaryDominated = CandFull;
                PR.Insts = Insts;
                return true;
            }
            // Admit loop headers as debt (see growRegion).
            if (Add == nullptr && Cand && Insts < MaxSize) {
                bool Retreating = true;
                if (auto It = AtomOf.find(Cand); It != AtomOf.end()) {
                    if (It->second->R.Blocks[0] != Cand)
                        Retreating = false;
                }
                else {
                    auto [CSize, CPinned] = Info.get(Cand);
                    if (CPinned || isa<ReturnInst>(Cand->getTerminator()))
                        Retreating = false;
                }
                if (Retreating) {
                    unsigned CandRPO = RPOIndex.lookup(Cand);
                    for (BasicBlock *P : predecessors(Cand)) {
                        if (PR.Set.count(P))
                            continue;
                        if (RPOIndex.lookup(P) <= CandRPO) {
                            Retreating = false;
                            break;
                        }
                    }
                }
                if (Retreating) {
                    addAtom(Cand);
                    continue;
                }
            }
            return false;
        }
        addAtom(Add);
    }
}

// One level of hierarchy construction: fold the given nodes (plus interstitial
// glue blocks) into parents of roughly Target instructions. Nodes that don't
// fit into any parent are returned unchanged.
static std::vector<HNode> formParents(Function &F, std::vector<HNode> Nodes,
                                      unsigned Target, BlockInfoCache &Info,
                                      const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    DenseMap<BasicBlock *, HNode *> AtomOf;
    for (HNode &N : Nodes)
        for (BasicBlock *B : N.R.Blocks)
            AtomOf[B] = &N;
    DenseMap<BasicBlock *, unsigned> RPOIndex;
    {
        ReversePostOrderTraversal<Function *> RPOT(&F);
        unsigned i = 0;
        for (BasicBlock *BB : RPOT)
            RPOIndex[BB] = i++;
    }
    SmallPtrSet<BasicBlock *, 32> Assigned;
    SmallPtrSet<HNode *, 16> Consumed;
    std::vector<HNode> Out;
    SmallVector<BasicBlock *, 8> StartQ;
    size_t ni = 0;
    while (true) {
        BasicBlock *E = nullptr;
        if (!StartQ.empty()) {
            E = StartQ.pop_back_val();
        }
        else {
            while (ni < Nodes.size() && Consumed.count(&Nodes[ni]))
                ni++;
            if (ni == Nodes.size())
                break;
            E = Nodes[ni++].R.Blocks[0];
        }
        if (E == &F.getEntryBlock() || Assigned.count(E))
            continue;
        if (auto It = AtomOf.find(E); It != AtomOf.end() && Consumed.count(It->second))
            continue;
        Region PR;
        SmallVector<HNode *, 8> Members;
        if (!growParent(E, Target, Info, AtomOf, Assigned, RPOIndex, PR, Members))
            continue;
        HNode P;
        P.R = std::move(PR);
        for (HNode *M : Members) {
            Consumed.insert(M);
            P.Kids.push_back(std::move(*M));
        }
        for (BasicBlock *B : P.R.Blocks)
            Assigned.insert(B);
        StartQ.push_back(P.R.Boundary);
        Out.push_back(std::move(P));
        ++SupersFormed;
    }
    for (HNode &N : Nodes)
        if (!Consumed.count(&N))
            Out.push_back(std::move(N));
    return Out;
}

// Prepare and extract one level of the hierarchy inside F, then recurse into
// each extracted parent to place its children. Children of a parent that
// could not be extracted are processed at this level instead.
static void processLevel(Function &F, std::vector<HNode> &Items,
                         const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    if (Items.empty())
        return;
    DominatorTree DT(F);
    SmallPtrSet<BasicBlock *, 32> Owned;
    for (HNode &N : Items)
        for (BasicBlock *B : N.R.Blocks)
            Owned.insert(B);
    DenseMap<Value *, bool> HighFanout;
    SmallPtrSet<HNode *, 16> Prepared;
    for (HNode &N : Items)
        if (prepareRegion(F, N.R, DT, Owned, HighFanout, ctx))
            Prepared.insert(&N);
    // Strip pre-existing lifetime markers: a marker whose block is extracted
    // would apply to a pointer argument rather than an alloca, and markers
    // are only stack-coloring hints (the GC lowering already deletes them on
    // frame-slot allocas).
    {
        SmallVector<IntrinsicInst *, 32> Lifetimes;
        for (Instruction &I : instructions(F))
            if (auto *II = dyn_cast<IntrinsicInst>(&I))
                if (II->getIntrinsicID() == Intrinsic::lifetime_start ||
                    II->getIntrinsicID() == Intrinsic::lifetime_end)
                    Lifetimes.push_back(II);
        for (IntrinsicInst *II : Lifetimes)
            II->eraseFromParent();
    }
    // CodeExtractor only consults the analysis cache to sink region-local
    // allocas into the callee (validating their lifetime markers with an
    // O(region) side-effect scan per alloca, on every extraction — quadratic
    // over hundreds of regions with thousands of allocas). We keep all
    // allocas in the caller by construction, so hand it an empty cache built
    // from a dummy function instead.
    Function *CEDummy = Function::Create(
        FunctionType::get(Type::getVoidTy(F.getContext()), false),
        GlobalValue::PrivateLinkage, "julia.split.ceac.dummy", F.getParent());
    ReturnInst::Create(F.getContext(),
                       BasicBlock::Create(F.getContext(), "", CEDummy));
    CodeExtractorAnalysisCache CEAC(*CEDummy);
    SmallVector<std::pair<HNode *, Function *>, 16> Sub;
    for (HNode &N : Items) {
        Function *NewF = nullptr;
        if (Prepared.count(&N))
            NewF = extractRegion(F, N.R, ctx, CEAC);
        if (!N.Kids.empty())
            Sub.push_back({&N, NewF});
    }
    CEDummy->eraseFromParent();
    for (auto &[N, NewF] : Sub)
        processLevel(NewF ? *NewF : F, N->Kids, ctx);
}

// Chunk one oversized straight-line block at low-live-count cut points (the
// resulting block boundaries are the cut points region formation needs).
static bool chunkBlock(Function &F, BasicBlock &BB, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    SmallVector<Instruction *, 0> Insts;
    Insts.reserve(BB.size());
    for (Instruction &I : BB)
        Insts.push_back(&I);
    unsigned n = Insts.size();
    unsigned C = std::max(16u, SplitChunkSize.getValue());
    if (n < 2 * C)
        return false;
    DenseMap<Instruction *, unsigned> LocalIdx;
    LocalIdx.reserve(n);
    for (unsigned i = 0; i < n; i++)
        LocalIdx[Insts[i]] = i;

    // Advisory liveness: for every potential cut position p (a cut before
    // Insts[p]), count values whose live interval spans p, split by boundary
    // kind. Illegal-to-cross values contribute to a barrier count instead.
    // Intervals are accumulated as +1/-1 diffs and prefix-summed.
    SmallVector<int32_t, 0> TrackedDiff(n + 2, 0), UntrackedDiff(n + 2, 0), BarrierDiff(n + 2, 0);
    SmallVector<uint8_t, 0> Pinned(n, 0);
    for (unsigned i = 0; i < n; i++) {
        if (isPinned(*Insts[i], ctx))
            Pinned[i] = 1;
    }
    auto addInterval = [&](SmallVectorImpl<int32_t> &Diff, unsigned Def, unsigned Last) JL_NOTSAFEPOINT {
        unsigned Hi = std::min(Last, n - 1);
        if (Hi > Def) {
            Diff[Def + 1] += 1;
            Diff[Hi + 1] -= 1;
        }
    };
    // Out-of-block values used here: live between their first and last use.
    DenseMap<Value *, std::pair<unsigned, unsigned>> ExtInterval;
    for (unsigned i = 0; i < n; i++) {
        for (Value *Op : Insts[i]->operands()) {
            if (!isa<Instruction>(Op) && !isa<Argument>(Op))
                continue;
            if (auto *OpI = dyn_cast<Instruction>(Op); OpI && OpI->getParent() == &BB)
                continue;
            auto It = ExtInterval.try_emplace(Op, i, i).first;
            It->second.second = i;
        }
    }
    for (auto &KV : ExtInterval) {
        switch (classifyType(KV.first->getType())) {
        case ValKind::Tracked:
            addInterval(TrackedDiff, KV.second.first, KV.second.second);
            break;
        case ValKind::CalleeRooted:
        case ValKind::TokenLike:
            addInterval(BarrierDiff, KV.second.first, KV.second.second);
            break;
        default:
            // Derived/Mixed inputs are as legal as untracked ones.
            addInterval(UntrackedDiff, KV.second.first, KV.second.second);
            break;
        }
    }
    // Root-buffer clusters (stores filling a stack buffer followed by the
    // call reading it) must not be separated by a cut: privatization (see
    // privatizeRootBuffers) requires each read's covering stores to sit in
    // the same region.
    {
        DenseMap<const Value *, unsigned> PendingRootStores;
        for (unsigned i = 0; i < n; i++) {
            if (auto *SI = dyn_cast<StoreInst>(Insts[i])) {
                const Value *Base = getUnderlyingObject(SI->getPointerOperand());
                if (isa<AllocaInst>(Base))
                    PendingRootStores.try_emplace(Base, i);
            }
            else if (auto *CB = dyn_cast<CallBase>(Insts[i])) {
                for (Value *Arg : CB->args()) {
                    if (!Arg->getType()->isPointerTy())
                        continue;
                    const Value *Base = getUnderlyingObject(Arg);
                    auto It = PendingRootStores.find(Base);
                    if (It != PendingRootStores.end()) {
                        addInterval(BarrierDiff, It->second, i);
                        PendingRootStores.erase(It);
                    }
                }
            }
        }
    }
    // In-block defs: live from def to last use; external users extend the
    // interval through the end of the block.
    for (unsigned i = 0; i < n; i++) {
        Instruction *I = Insts[i];
        if (I->use_empty())
            continue;
        unsigned Last = i;
        bool Ext = false;
        for (User *U : I->users()) {
            auto *UI = cast<Instruction>(U);
            if (UI->getParent() == &BB) {
                auto It = LocalIdx.find(UI);
                if (It != LocalIdx.end() && It->second > Last)
                    Last = It->second;
            }
            else {
                Ext = true;
            }
        }
        if (Ext)
            Last = n;
        switch (classifyType(I->getType())) {
        case ValKind::Tracked:
            addInterval(TrackedDiff, i, Last);
            break;
        case ValKind::Untracked:
            addInterval(UntrackedDiff, i, Last);
            break;
        case ValKind::Derived: {
            // Whether the spine is rematerializable is checked for real at
            // prepare time; approximate it here for cut placement.
            bool CloneOK = isa<GetElementPtrInst>(I) || isa<AddrSpaceCastInst>(I) ||
                           isa<BitCastInst>(I);
            if (!CloneOK)
                if (auto *CI = dyn_cast<CallInst>(I))
                    CloneOK = ctx.gc_loaded_func && CI->getCalledFunction() == ctx.gc_loaded_func;
            addInterval(CloneOK ? UntrackedDiff : BarrierDiff, i, Last);
            break;
        }
        default:
            addInterval(BarrierDiff, i, Last);
            break;
        }
    }
    SmallVector<int32_t, 0> TrackedPS(n + 1, 0), UntrackedPS(n + 1, 0), BarrierPS(n + 1, 0);
    for (unsigned p = 1; p <= n; p++) {
        TrackedPS[p] = TrackedPS[p - 1] + TrackedDiff[p];
        UntrackedPS[p] = UntrackedPS[p - 1] + UntrackedDiff[p];
        BarrierPS[p] = BarrierPS[p - 1] + BarrierDiff[p];
    }

    // Pick cuts: mandatory cuts fencing off runs of pinned instructions, and
    // within each straight-line span, greedy min-live-score cuts about every
    // SplitChunkSize instructions. Tracked values weigh heavier: they cost GC
    // roots at the new safepoint, not just an argument slot.
    SmallVector<unsigned, 32> Cuts;
    auto pushCut = [&](unsigned p) JL_NOTSAFEPOINT {
        if (p >= 1 && p <= n - 1 && !isa<PHINode>(Insts[p]) &&
            (Cuts.empty() || Cuts.back() < p))
            Cuts.push_back(p);
    };
    auto score = [&](unsigned p) JL_NOTSAFEPOINT {
        return 4 * TrackedPS[p] + UntrackedPS[p];
    };
    auto emitSpanCuts = [&](unsigned s, unsigned e) JL_NOTSAFEPOINT {
        unsigned q = s;
        while (e - q > C + C / 2) {
            unsigned lo = q + C / 2;
            unsigned hi = std::min(q + C + C / 2, e - 1);
            int Best = -1;
            for (unsigned p = lo; p <= hi; p++)
                if (!BarrierPS[p] && !isa<PHINode>(Insts[p]) &&
                    (Best < 0 || score(p) < score((unsigned)Best)))
                    Best = (int)p;
            if (Best < 0) {
                for (unsigned p = hi + 1; p < e; p++)
                    if (!BarrierPS[p] && !isa<PHINode>(Insts[p])) {
                        Best = (int)p;
                        break;
                    }
            }
            if (Best < 0)
                return;
            pushCut((unsigned)Best);
            q = (unsigned)Best;
        }
    };
    {
        unsigned SpanStart = 0;
        unsigned i = 0;
        unsigned end = n - 1; // never cut after the terminator
        while (i < end) {
            if (!Pinned[i]) {
                i++;
                continue;
            }
            unsigned j = i;
            while (j < end && Pinned[j])
                j++;
            emitSpanCuts(SpanStart, i);
            pushCut(i);
            pushCut(j);
            SpanStart = j;
            i = j;
        }
        emitSpanCuts(SpanStart, end);
    }
    if (Cuts.empty())
        return false;

    ++BlocksChunked;
    // Split back to front: each splitBasicBlock splices the tail of the block
    // into the new one (an O(moved) walk), so front-to-back order re-walks the
    // remaining tail per cut, O(n^2/C) on huge blocks.
    for (unsigned k = Cuts.size(); k-- > 0;)
        BB.splitBasicBlock(Insts[Cuts[k]]->getIterator(), BB.getName() + ".chunk");
    return true;
}

// Grow a region from Entry by repeatedly adding blocks whose predecessors all
// lie inside the group. A cut is possible when exactly one escape target has
// all of its predecessors inside the group; that block becomes the boundary.
static bool growRegion(BasicBlock *Entry, unsigned Target, BlockInfoCache &Info,
                       const SmallPtrSetImpl<BasicBlock *> &Assigned,
                       const DenseMap<BasicBlock *, unsigned> &RPOIndex,
                       Region &R) JL_NOTSAFEPOINT
{
    auto [ESize, EPinned] = Info.get(Entry);
    if (EPinned || isa<ReturnInst>(Entry->getTerminator()))
        return false;
    unsigned MinSize = std::max(16u, Target / 4);
    unsigned MaxSize = 4 * Target;
    const unsigned MaxBlocks = std::max(16u, SplitMaxRegionBlocks.getValue());

    R.Blocks.push_back(Entry);
    R.Set.insert(Entry);
    unsigned Insts = ESize;
    // Escape targets: number of edges into them from inside R, plus their
    // total predecessor edge count.
    DenseMap<BasicBlock *, std::pair<unsigned, unsigned>> Fringe;
    // Edges from outside into non-entry members: nonzero while a loop is only
    // partially absorbed. Cutting is only legal at zero (single entry).
    unsigned Pending = 0;
    auto addBlock = [&](BasicBlock *B) JL_NOTSAFEPOINT {
        R.Set.insert(B);
        R.Blocks.push_back(B);
        Fringe.erase(B);
        for (BasicBlock *P : predecessors(B))
            if (!R.Set.count(P))
                Pending++;
        for (BasicBlock *S : successors(B)) {
            if (R.Set.count(S)) {
                if (S != Entry && S != B)
                    Pending--;
                continue;
            }
            auto &FE = Fringe[S];
            if (FE.second == 0)
                FE.second = std::distance(pred_begin(S), pred_end(S));
            FE.first++;
        }
    };
    {
        // Seed (Entry's incoming edges are the region entry, not debt).
        R.Set.erase(Entry);
        R.Blocks.clear();
        R.Set.insert(Entry);
        R.Blocks.push_back(Entry);
        for (BasicBlock *S : successors(Entry)) {
            if (S == Entry)
                continue;
            auto &FE = Fringe[S];
            if (FE.second == 0)
                FE.second = std::distance(pred_begin(S), pred_end(S));
            FE.first++;
        }
    }
    while (true) {
        BasicBlock *Add = nullptr;
        unsigned AddIdx = ~0u;
        BasicBlock *Cand = nullptr;
        unsigned CandIdx = ~0u;
        unsigned NumCand = 0;
        bool CandFull = false;
        for (auto &FE : Fringe) {
            BasicBlock *S = FE.first;
            bool Full = FE.second.first == FE.second.second;
            if (Assigned.count(S))
                continue; // owned by another region; can't add or split it
            // Any non-cold escape target can be a boundary (the rest become
            // extra exits of the extracted function). Prefer targets whose
            // predecessors are all inside, then the earliest in RPO, which is
            // the likeliest hot continuation.
            if (!Info.isCold(S)) {
                unsigned Idx = RPOIndex.lookup(S);
                if (!Cand || (Full && !CandFull) ||
                    (Full == CandFull && Idx < CandIdx)) {
                    Cand = S;
                    CandIdx = Idx;
                    CandFull = Full;
                }
                NumCand++;
            }
            if (!Full)
                continue; // can't add yet: some predecessors outside the group
            auto [SSize, SPinned] = Info.get(S);
            if (SPinned || isa<ReturnInst>(S->getTerminator()))
                continue; // may act as a boundary, but must stay in the caller
            unsigned Idx = RPOIndex.lookup(S);
            if (!Add || Idx < AddIdx) {
                Add = S;
                AddIdx = Idx;
            }
        }
        bool CanCut = Cand != nullptr && Pending == 0;
        // Under -julia-split-single-exit-cuts, hold out for a reconvergence
        // point (one hot escape) once the target is reached; the clamp-bail
        // path below still accepts multi-exit cuts so growth cannot fail more
        // often than before.
        bool WantCut = CanCut && (!SplitSingleExitCuts || NumCand == 1);
        if (WantCut && Insts >= Target) {
            R.Boundary = Cand;
            R.BoundaryDominated = CandFull;
            R.Insts = Insts;
            GrowCutTarget++;
            return true;
        }
        if (!Add || Insts >= MaxSize || R.Blocks.size() >= MaxBlocks) {
            // When growth stopped against a clamp (rather than getting stuck),
            // any legal cut beats forming no region at all: with MinSize
            // unreachable inside the clamp, insisting on it made oversized
            // targets silently no-op on fine-grained CFGs.
            bool Clamped = Insts >= MaxSize || R.Blocks.size() >= MaxBlocks;
            if (CanCut && (Insts >= MinSize || Clamped)) {
                R.Boundary = Cand;
                R.BoundaryDominated = CandFull;
                R.Insts = Insts;
                GrowCutClamp++;
                return true;
            }
            // Loop headers can only be entered as debt: admit the candidate
            // when its unabsorbed predecessors are all retreating edges (loop
            // backedges); the debt clears once the loop body is inside.
            if (Add == nullptr && Cand && Insts < MaxSize &&
                R.Blocks.size() < MaxBlocks) {
                auto [CSize, CPinned] = Info.get(Cand);
                bool Retreating = !CPinned && !isa<ReturnInst>(Cand->getTerminator());
                if (Retreating) {
                    unsigned CandRPO = RPOIndex.lookup(Cand);
                    for (BasicBlock *P : predecessors(Cand)) {
                        if (R.Set.count(P))
                            continue;
                        if (RPOIndex.lookup(P) <= CandRPO) {
                            Retreating = false;
                            break;
                        }
                    }
                }
                if (Retreating) {
                    addBlock(Cand);
                    Insts += Info.get(Cand).first;
                    continue;
                }
            }
            if (R.Blocks.size() >= MaxBlocks)
                GrowFailBlocks++;
            else if (Insts >= MaxSize)
                GrowFailSize++;
            else
                GrowFailNoAdd++;
            return false;
        }
        addBlock(Add);
        Insts += Info.get(Add).first;
    }
}

static void formRegions(Function &F, BlockInfoCache &Info,
                        std::vector<Region> &Regions) JL_NOTSAFEPOINT
{
    DenseMap<BasicBlock *, unsigned> RPOIndex;
    SmallVector<BasicBlock *, 0> Order;
    {
        ReversePostOrderTraversal<Function *> RPOT(&F);
        for (BasicBlock *BB : RPOT) {
            RPOIndex[BB] = Order.size();
            Order.push_back(BB);
        }
    }
    unsigned C = std::max(16u, SplitChunkSize.getValue());
    SmallPtrSet<BasicBlock *, 32> Assigned;
    SmallVector<BasicBlock *, 8> StartQ;
    size_t oi = 0;
    while (true) {
        BasicBlock *E = nullptr;
        if (!StartQ.empty()) {
            E = StartQ.pop_back_val();
        }
        else {
            while (oi < Order.size() &&
                   (Assigned.count(Order[oi]) || Order[oi] == &F.getEntryBlock()))
                oi++;
            if (oi >= Order.size())
                break;
            E = Order[oi++];
        }
        if (Assigned.count(E) || E == &F.getEntryBlock())
            continue;
        Region R;
        if (!growRegion(E, C, Info, Assigned, RPOIndex, R))
            continue;
        // Give the region a dedicated caller-resident pre-header when its
        // entry doesn't already have a unique fall-through predecessor:
        // spill fills and hoisted rematerializations live there.
        {
            SmallSetVector<BasicBlock *, 8> OutsidePreds;
            for (BasicBlock *P : predecessors(E))
                if (!R.Set.count(P))
                    OutsidePreds.insert(P);
            if (!OutsidePreds.empty() &&
                (OutsidePreds.size() != 1 ||
                 OutsidePreds[0]->getSingleSuccessor() != E)) {
                BasicBlock *Pre = SplitBlockPredecessors(
                    E, OutsidePreds.getArrayRef(), ".pre");
                if (Pre) {
                    Info.invalidate(E);
                    RPOIndex[Pre] = RPOIndex.lookup(E);
                }
            }
        }
        // Split the boundary: PHIs (plus later spill fills/reloads and remat
        // clones) stay in the caller-resident head; the rest of the block
        // seeds the next region.
        BasicBlock *T = R.Boundary;
        BasicBlock *TBody = T->splitBasicBlock(T->getFirstNonPHIIt(), T->getName() + ".cont");
        Info.invalidate(T);
        RPOIndex[TBody] = RPOIndex.lookup(T);
        for (BasicBlock *B : R.Blocks)
            Assigned.insert(B);
        Regions.push_back(std::move(R));
        ++RegionsFormed;
        StartQ.push_back(TBody);
    }
}

static bool splitFunction(Function &F, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    bool BigBlocks = false;
    if (SplitBlockThreshold) {
        for (BasicBlock &BB : F) {
            if (BB.size() > SplitBlockThreshold) {
                BigBlocks = true;
                break;
            }
        }
    }
    bool Qualifies = BigBlocks || (SplitFunctionThreshold &&
                                   F.getInstructionCount() > SplitFunctionThreshold);
    if (!Qualifies)
        return false;
    bool Changed = false;
    auto now = []() JL_NOTSAFEPOINT { return std::chrono::steady_clock::now(); };
    auto ms = [](auto a, auto b) JL_NOTSAFEPOINT {
        return std::chrono::duration_cast<std::chrono::milliseconds>(b - a).count();
    };
    auto T0 = now();
    GrowCutTarget = GrowCutClamp = GrowFailBlocks = GrowFailSize = GrowFailNoAdd = 0;
    IfaceIn = IfaceOut = IfaceInMax = IfaceOutMax = IfaceExits = IfaceCalls = 0;
    if (BigBlocks) {
        SmallVector<BasicBlock *, 4> Oversized;
        for (BasicBlock &BB : F)
            if (BB.size() > SplitBlockThreshold)
                Oversized.push_back(&BB);
        for (BasicBlock *BB : Oversized)
            Changed |= chunkBlock(F, *BB, ctx);
    }
    auto T1 = now();
    BlockInfoCache Info(ctx);
    std::vector<Region> Regions;
    formRegions(F, Info, Regions);
    auto T2 = now();
    if (SplitDebug || SplitTime) {
        SmallVector<unsigned, 64> Sizes;
        for (Region &R : Regions)
            Sizes.push_back(R.Insts);
        llvm::sort(Sizes);
        errs() << "julia-function-splitting: " << F.getName() << ": formed "
               << Regions.size() << " regions";
        if (!Sizes.empty())
            errs() << " insts min/med/max=" << Sizes.front() << "/"
                   << Sizes[Sizes.size() / 2] << "/" << Sizes.back();
        errs() << " cuts(target/clamp)=" << GrowCutTarget << "/" << GrowCutClamp
               << " growfail(blocks/size/stuck)=" << GrowFailBlocks << "/"
               << GrowFailSize << "/" << GrowFailNoAdd << "\n";
    }
    if (Regions.empty())
        return Changed;
    privatizeRootBuffers(F, Regions);
    sinkEntryAllocas(F, Regions);
    // Build the hierarchical decomposition up front: regions become atomic
    // nodes and are folded, together with the glue blocks between them, into
    // parents by the same interval growth, level by level, so that no
    // function at any level retains more than about GroupSize callsites.
    std::vector<HNode> Level;
    Level.reserve(Regions.size());
    for (Region &R : Regions) {
        HNode N;
        N.R = std::move(R);
        Level.push_back(std::move(N));
    }
    unsigned LevelTarget = std::max(16u, SplitChunkSize.getValue());
    while (SplitGroupSize && Level.size() > SplitGroupSize) {
        size_t Before = Level.size();
        LevelTarget *= SplitGroupSize;
        Level = formParents(F, std::move(Level), LevelTarget, Info, ctx);
        if (Level.size() >= Before)
            break; // no progress
    }
    auto T3 = now();
    if (SplitDebug || SplitTime)
        errs() << "julia-function-splitting: " << F.getName() << ": top level has "
               << Level.size() << " nodes\n";
    processLevel(F, Level, ctx);
    auto T5 = now();
    if (SplitDebug || SplitTime)
        errs() << "julia-function-splitting: times(ms) chunk=" << ms(T0, T1)
               << " form=" << ms(T1, T2) << " group=" << ms(T2, T3)
               << " process=" << ms(T3, T5)
               << " [remat=" << PrepRematMs / 1000 << " ce=" << PrepCEMs / 1000
               << " io=" << PrepIOMs / 1000 << " spill=" << PrepSpillMs / 1000
               << "] insts=" << F.getInstructionCount() << " iface(in avg/max="
               << (IfaceCalls ? IfaceIn / IfaceCalls : 0) << "/" << IfaceInMax
               << " out avg/max=" << (IfaceCalls ? IfaceOut / IfaceCalls : 0)
               << "/" << IfaceOutMax << " exits avg x100="
               << (IfaceCalls ? 100 * IfaceExits / IfaceCalls : 0) << ")\n";
    assert(!verifyFunction(F, &errs()));
    return true;
}

// EXPERIMENT(boundary-tax): while region k executes (hundreds of cycles),
// prefetch the head of region k+1's code so its entry hits L2 instead of
// demand-missing to L3. Layout order of a glue function's region calls
// approximates execution order (the glue CFG is essentially linear with
// exit branches). locality=2 -> prefetcht1 on x86 (fill L2, not L1d);
// cache type "data" because x86 drops instruction-type prefetches, and the
// L2 is unified so code fetch hits lines a data prefetch brought in.
static void insertRegionPrefetches(Function &F) JL_NOTSAFEPOINT
{
    SmallVector<CallInst *, 32> Calls;
    for (BasicBlock &BB : F)
        for (Instruction &I : BB)
            if (auto *CI = dyn_cast<CallInst>(&I))
                if (Function *Callee = CI->getCalledFunction())
                    if (!Callee->isDeclaration() && Callee->getName().contains("julia_split"))
                        Calls.push_back(CI);
    if (Calls.size() < 2)
        return;
    LLVMContext &Ctx = F.getContext();
    Type *I8 = Type::getInt8Ty(Ctx);
    for (size_t i = 0; i + 1 < Calls.size(); i++) {
        Function *Next = Calls[i + 1]->getCalledFunction();
        IRBuilder<> B(Calls[i]);
        for (unsigned l = 0; l < SplitPrefetchLines; l++) {
            Value *P = B.CreateGEP(I8, Next, B.getInt64((uint64_t)l * 64));
            B.CreateIntrinsic(Intrinsic::prefetch, {P->getType()},
                              {P, B.getInt32(0), B.getInt32(2), B.getInt32(1)});
        }
    }
}

} // anonymous namespace

PreservedAnalyses FunctionSplittingPass::run(Module &M, ModuleAnalysisManager &AM)
{
    if (SplitBlockThreshold == 0 && SplitFunctionThreshold == 0)
        return PreservedAnalyses::all();
    JuliaPassContext ctx;
    ctx.initFunctions(M);
    // Snapshot the worklist: extraction adds new (already small) functions.
    SmallVector<Function *, 16> Work;
    for (Function &F : M)
        if (!F.isDeclaration() && !F.hasFnAttribute(Attribute::OptimizeNone))
            Work.push_back(&F);
    bool Changed = false;
    for (Function *F : Work)
        Changed |= splitFunction(*F, ctx);
    if (Changed && SplitPrefetchLines)
        for (Function &F : M)
            if (!F.isDeclaration())
                insertRegionPrefetches(F);
    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
