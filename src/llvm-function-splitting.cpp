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
// Interface lowering contract (implemented by spillInterface): this pass,
// not CodeExtractor, owns how values cross a region boundary, because the
// data interface carries all the Julia-specific knowledge (GC slot typing,
// register-vs-memory strategy, vectorizable marshalling). CodeExtractor
// provides control-flow surgery only: function construction and block
// moving, input-to-argument remapping, multi-exit lowering to return codes
// plus the caller-side switch, extraction legality, and debug-info fixup.
// Once a region's interface has been spilled, the only SSA values still
// crossing its boundary are direct inputs (which extraction turns into
// arguments, riding in registers) — every spilled input, every escaping
// value and every boundary-head phi crosses through the two caller-frame
// aggregates instead. CodeExtractor's own output marshalling (one scalar
// alloca, pointer argument and lifetime-marker pair per value) must see
// zero outputs for such regions, except for the deliberate leftovers:
//   * regions with fewer than SplitOutputSpillMin outputs (never spilled;
//     the scalar path is fine at that size),
//   * escape kinds that cannot be slotted (rejected or rematerialized
//     before spilling ever runs).
// Any other value reaching CodeExtractor's output path means the interface
// was only half-lowered and is being marshalled twice — the boundary-phi
// hole this contract was written after — and shows up as a nonzero
// "out avg" for spilled regions in the -julia-split-time statistics.
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
#include <llvm/IR/ValueHandle.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/Support/Debug.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/CodeExtractor.h>
#include <llvm/Transforms/Utils/PromoteMemToReg.h>
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

//===----------------------------------------------------------------------===//
// Triggers: when does the pass act on a function at all?
//
// Both default to 0 = the pass is entirely disabled. Once triggered, whether a
// function is actually OUTLINED is decided by the sizing caps below (a
// function already under every cap satisfies every per-function cost bound the
// caps enforce, so it is left alone); oversized blocks are chunked regardless.
//===----------------------------------------------------------------------===//

static cl::opt<unsigned> SplitBlockThreshold(
    "julia-split-block-threshold", cl::init(8192), cl::Hidden,
    cl::desc("Chunk basic blocks with more instructions than this and consider "
             "the containing function for outlining (0 = disabled)"));

static cl::opt<unsigned> SplitFunctionThreshold(
    "julia-split-function-threshold", cl::init(512), cl::Hidden,
    cl::desc("Consider functions with more instructions than this for "
             "outlining (0 = disabled). Whether outlining happens is decided "
             "by the sizing caps below; a function whose instruction count is "
             "at or below the smallest cap can never exceed any cap (blocks "
             "and safepoints are bounded by instructions), so the default "
             "skips only provably-inert functions"));

//===----------------------------------------------------------------------===//
// Sizing caps: the primary tunables.
//
// Each cap is a per-function compile-cost model for one class of superlinear
// pass: instructions (value numbering, SLP, instruction selection),
// safepoints (register allocation of rooted live ranges), and basic blocks
// (CFG-walk analyses such as GVN's non-local memory dependencies). Blocks are
// chunked to the block-insts/block-safepoints quantum; regions grow until any
// region-* cap fills. Defaults were tuned on the workloads in
// splitting_MWEs/ (see its README for the measured curves).
//===----------------------------------------------------------------------===//

static cl::opt<unsigned> SplitBlockInsts(
    "julia-split-block-insts", cl::init(8192), cl::Hidden,
    cl::desc("Instruction spacing of the block cut quantum: oversized basic "
             "blocks are chunked so no block spans more than about this many "
             "instructions"));

static cl::opt<unsigned> SplitBlockSafepoints(
    "julia-split-block-safepoints", cl::init(512), cl::Hidden,
    cl::desc("Cut oversized blocks so that no chunk (and no re-merged block) "
             "spans more than about this many safepoint calls, independently "
             "of the instruction spacing. Register allocation cost is "
             "superlinear in the rooted live ranges crossing the calls of a "
             "single block, so call-dense code needs a finer cut quantum than "
             "instruction count alone provides; this also keeps the "
             "region-level safepoint budget realizable from whole blocks. "
             "0 disables"));

static cl::opt<unsigned> SplitRegionInsts(
    "julia-split-region-insts", cl::init(65536), cl::Hidden,
    cl::desc("Instruction growth target for regions, decoupled from the block "
             "cut spacing (-julia-split-block-insts). Call-free regions want to "
             "grow well beyond the block quantum (the boundary runtime tax "
             "falls as 1/R), and call-dense regions are bounded by "
             "-julia-split-region-safepoints instead. "
             "0 inherits -julia-split-block-insts"));

static cl::opt<unsigned> SplitRegionSafepoints(
    "julia-split-region-safepoints", cl::init(512), cl::Hidden,
    cl::desc("Cut region growth once a region spans about this many safepoint "
             "calls, independently of the instruction target. The per-region "
             "compile cost on call-dense code is superlinear in region size "
             "(MachineCSE, GreedyRA), so call-dense regions must stay small "
             "even when the instruction target is large. 0 disables"));

static cl::opt<unsigned> SplitRegionBlocks(
    "julia-split-region-blocks", cl::init(512), cl::Hidden,
    cl::desc("Cut region growth once a region spans about this many basic "
             "blocks, independently of the instruction and safepoint targets. "
             "The per-region compile cost of the CFG-walk passes (notably GVN, "
             "whose non-local memory-dependency analysis PHI-translates each "
             "load across the region's blocks) grows as instructions x blocks, "
             "so branchy block-dense code (e.g. tracked automatic "
             "differentiation) needs a block-count bound even when the "
             "instruction target is large. 0 disables"));

// Effective region instruction target (region sizing is independent of the
// block cut quantum; the flag inherits the chunk size when unset).
static unsigned regionSizeTarget() JL_NOTSAFEPOINT
{
    unsigned T = SplitRegionInsts ? SplitRegionInsts.getValue()
                                  : SplitBlockInsts.getValue();
    return std::max(16u, T);
}

//===----------------------------------------------------------------------===//
// Mechanism knobs: interface sizing and growth bounds. Rarely need tuning.
//===----------------------------------------------------------------------===//

static cl::opt<unsigned> SplitGroupSize(
    "julia-split-group-size", cl::init(24), cl::Hidden,
    cl::desc("Number of regions grouped into each parent of the hierarchical "
             "decomposition (0 = flat splitting)"));

static cl::opt<unsigned> SplitDirectArgLimit(
    "julia-split-direct-arg-limit", cl::init(64), cl::Hidden,
    cl::desc("Maximum region interface size passed directly as arguments/output "
             "pointers before spilling through in-memory aggregates"));

static cl::opt<unsigned> SplitOutputSpillMin(
    "julia-split-output-spill-min", cl::init(2), cl::Hidden,
    cl::desc("Spill region outputs through the aggregate whenever a region has "
             "at least this many (0 = only with the full wide-interface spill). "
             "Contiguous slots let one pointer replace per-output pointer "
             "arguments and keep the marshalling vectorizable"));

static cl::opt<unsigned> SplitEntryFactor(
    "julia-split-entry-factor", cl::init(4), cl::Hidden,
    cl::desc("Outline only when the function exceeds a region cap by this "
             "factor. Functions between 1x and Kx a cap compile acceptably "
             "unsplit, while outlining them pays the flat per-region stack "
             "tax over too little extracted mass; past Kx the caps' "
             "superlinear compile costs dominate and outlining wins."));

static cl::opt<unsigned> SplitMinCutWindow(
    "julia-split-mincut-window", cl::init(2), cl::Hidden,
    cl::desc("When a region cap forces a cut, choose the boundary with the "
             "narrowest live interface among the grow prefixes whose fill (on "
             "the axis that triggered the cut) is at least the final fill "
             "divided by this factor (0 = always cut exactly at the cap)"));

static cl::opt<unsigned> SplitMaxRegionBlocks(
    "julia-split-max-region-blocks", cl::init(4096), cl::Hidden,
    cl::desc("Maximum number of basic blocks a region may absorb (bounds the "
             "growth scan). Regions that hit this clamp cut at the best legal "
             "point instead of the size target; clamp cuts are counted and "
             "reported under -julia-split-time so parameter sweeps see the "
             "realized region sizes rather than the requested target"));

//===----------------------------------------------------------------------===//
// Diagnostics and debugging kill-switches.
//===----------------------------------------------------------------------===//

static cl::opt<bool> SplitDebug(
    "julia-split-debug", cl::init(false), cl::Hidden,
    cl::desc("Print region formation/rejection diagnostics (note: printing "
             "instructions builds a module slot tracker and is very slow on "
             "big modules)"));

static cl::opt<bool> SplitTime(
    "julia-split-time", cl::init(false), cl::Hidden,
    cl::desc("Print per-stage timing for the pass"));

// Kill-switches for bisecting miscompiles to a single mechanism.
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
static cl::opt<bool> SplitNoSeamMerge(
    "julia-split-no-seam-merge", cl::init(false), cl::Hidden,
    cl::desc("Diagnostic: skip straight-seam merging (leaves the seams "
             "InstCombine can sink chains across; isolates the LLVM fix)"));
static cl::opt<int> SplitSpillMax(
    "julia-split-spill-max", cl::init(-1), cl::Hidden,
    cl::desc("Only spill the first N regions that request it (-1 = unlimited)"));

namespace {

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

static bool isSafepointCall(const Instruction &I, const JuliaPassContext &ctx) JL_NOTSAFEPOINT;

// Lazily computed per-block size, safepoint count and pinnedness (blocks are
// created during splitting, so this must tolerate new blocks).
struct BlockInfo {
    unsigned Size;
    unsigned Safepoints;
    bool Pinned;
};
struct BlockInfoCache {
    const JuliaPassContext &ctx;
    DenseMap<BasicBlock *, BlockInfo> M;
    BlockInfoCache(const JuliaPassContext &ctx) JL_NOTSAFEPOINT : ctx(ctx) {}
    BlockInfo get(BasicBlock *BB) JL_NOTSAFEPOINT
    {
        auto It = M.find(BB);
        if (It != M.end())
            return It->second;
        BlockInfo BI{0, 0, false};
        for (Instruction &I : *BB) {
            BI.Size++;
            if (isSafepointCall(I, ctx))
                BI.Safepoints++;
            if (!BI.Pinned && isPinned(I, ctx))
                BI.Pinned = true;
        }
        return M[BB] = BI;
    }
    void invalidate(BasicBlock *BB) JL_NOTSAFEPOINT { M.erase(BB); }
    // Drop all per-block sizes (after CFG surgery such as block chunking);
    // entries recompute lazily. Cold-ness is preserved: chunking only chains
    // a block through unconditional seams, which cannot change whether every
    // path from it ends in unreachable.
    void invalidateSizes() JL_NOTSAFEPOINT { M.clear(); }

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
    if (Escaping.empty())
        return true;
    // Hoisted clones are SSA values: they must not land inside another
    // region, whose extraction would turn them into illegal derived outputs
    // (regionPreheader excludes owned blocks).
    BasicBlock *Pred = regionPreheader(R, Owned);

    // Validate everything before mutating anything.
    SmallVector<Instruction *, RematSpineLimit> HoistSpine, SiteSpine;
    SmallPtrSet<Instruction *, 16> HoistSet, SiteSet;
    for (Instruction *I : Escaping) {
        if (!SplitNoHoistRemat && Pred &&
            collectHoistSpine(I, R, Pred, DT, HoistSpine, HoistSet, ctx))
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

    LLVMContext &Ctx = F.getContext();
    Type *T_prjlvalue = PointerType::get(Ctx, AddressSpace::Tracked);
    // (Pred is non-null whenever HoistSpine is non-empty — collectHoistSpine
    // only runs with a preheader — but spelled out for the static analyzer.)
    if (Pred && !HoistSpine.empty()) {
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
    // Opportunistic tier: tracked/untracked escaping values whose whole
    // in-region dependency cone is clonable (address computation and
    // immutable loads) are cheaper to recompute in the preheader than to
    // route through the interface -- each escaping value costs an interface
    // slot (for tracked values a caller GC frame slot, pinned for the
    // buffer's whole live range) plus marshalling at every call. Replace
    // only their EXTERNAL uses with the preheader recomputation; the region
    // keeps computing its internal copy, so no new input appears either.
    // Failures just leave the value to the normal interface.
    if (Pred && !SplitNoHoistRemat) {
        SmallVector<Instruction *, 16> OppTops;
        for (BasicBlock *BB : R.Blocks) {
            for (Instruction &I : *BB) {
                ValKind K = classifyType(I.getType());
                if (K != ValKind::Tracked && K != ValKind::Untracked)
                    continue;
                if (HoistSet.count(&I) || SiteSet.count(&I))
                    continue;
                for (Use &U : I.uses()) {
                    if (!R.Set.count(useBlock(U))) {
                        OppTops.push_back(&I);
                        break;
                    }
                }
            }
        }
        SmallVector<Instruction *, 32> OppSpine;
        SmallPtrSet<Instruction *, 32> OppSet;
        SmallPtrSet<Instruction *, 16> OppReplaced;
        for (Instruction *I : OppTops) {
            SmallVector<Instruction *, RematSpineLimit> Scratch;
            if (collectHoistSpine(I, R, Pred, DT, Scratch, OppSet, ctx)) {
                OppSpine.append(Scratch.begin(), Scratch.end());
                OppReplaced.insert(I);
            }
            else {
                // collectHoistSpine records exactly the instructions it
                // appended; scrub them so a later candidate re-validates
                // (an OppSet entry missing from OppSpine would leave a
                // clone's operand pointing back into the region).
                for (Instruction *SI : Scratch)
                    OppSet.erase(SI);
            }
        }
        if (!OppSpine.empty()) {
            ValueToValueMapTy VMap;
            BasicBlock::iterator IP = Pred->getTerminator()->getIterator();
            for (Instruction *I : OppSpine) {
                Instruction *Clone = I->clone();
                Clone->setName(I->getName() + ".remat");
                Clone->insertBefore(IP);
                RemapInstruction(Clone, VMap,
                                 RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
                VMap[I] = Clone;
            }
            for (Instruction *I : OppSpine) {
                if (!OppReplaced.count(I))
                    continue;
                SmallVector<Use *, 8> ExtUses;
                for (Use &U : I->uses())
                    if (!R.Set.count(useBlock(U)))
                        ExtUses.push_back(&U);
                for (Use *U : ExtUses)
                    U->set(VMap[I]);
            }
        }
    }
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
    return true;
}

// Memory-demotion utilities in the style of llvm::DemoteRegToStack /
// llvm::DemotePHIToStack, except that the demoted value lives in a
// caller-provided aggregate slot instead of a fresh alloca. The slot address
// is materialized at every store/load site via MakeSlot (a single GEP per
// site; entry-block GEPs would accumulate O(interface) code in the outermost
// caller).

// Lower an SSA value into its slot: store it right after its definition (the
// value stays live in SSA until then, so GC lowering keeps it rooted and the
// slot always holds the most recent def) and replace every use classified by
// IsExternal with a reload materialized at the use site. Reading back where
// the value is needed — rather than once at a fixed point such as a region
// boundary — stays correct when the reader sits on a cycle and can execute
// before the definition has run.
static void DemoteRegToAggregateSlot(Instruction &I, MaybeAlign A,
                                     function_ref<Value *(IRBuilder<> &)> MakeSlot,
                                     function_ref<bool(Use &)> IsExternal) JL_NOTSAFEPOINT
{
    BasicBlock::iterator StoreIP = isa<PHINode>(I)
                                       ? I.getParent()->getFirstInsertionPt()
                                       : std::next(I.getIterator());
    IRBuilder<> SB(I.getParent(), StoreIP);
    SB.CreateAlignedStore(&I, MakeSlot(SB), A);
    SmallVector<Use *, 8> ExtUses;
    for (Use &U : I.uses())
        if (IsExternal(U))
            ExtUses.push_back(&U);
    for (Use *U : ExtUses) {
        auto *UI = cast<Instruction>(U->getUser());
        BasicBlock::iterator IP;
        if (auto *PN = dyn_cast<PHINode>(UI))
            IP = PN->getIncomingBlock(*U)->getTerminator()->getIterator();
        else
            IP = UI->getIterator();
        IRBuilder<> B(IP->getParent(), IP);
        auto *L = B.CreateAlignedLoad(I.getType(), MakeSlot(B), A, I.getName() + ".out");
        U->set(L);
    }
}

// Lower a PHI into its slot: store each incoming value at the end of its
// incoming block — exactly one of those runs per traversal, so the slot
// always holds the value of the edge actually taken, on cycles too — and
// replace the PHI with a load of the slot at its own position. Duplicate
// incoming blocks (switches) carry identical values per LLVM's PHI rules, so
// one store per predecessor suffices.
static void DemotePHIToAggregateSlot(PHINode &PN, MaybeAlign A,
                                     function_ref<Value *(IRBuilder<> &)> MakeSlot) JL_NOTSAFEPOINT
{
    SmallPtrSet<BasicBlock *, 8> Stored;
    for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; i++) {
        BasicBlock *In = PN.getIncomingBlock(i);
        if (!Stored.insert(In).second)
            continue;
        IRBuilder<> B(In->getTerminator());
        B.CreateAlignedStore(PN.getIncomingValue(i), MakeSlot(B), A);
    }
    BasicBlock *BB = PN.getParent();
    IRBuilder<> LB(BB, BB->getFirstInsertionPt());
    auto *L = LB.CreateAlignedLoad(PN.getType(), MakeSlot(LB), A, PN.getName() + ".phi");
    PN.replaceAllUsesWith(L);
    PN.eraseFromParent();
}

// Implementation of the interface lowering contract (see the file header).
// Reduce an oversized region interface by passing values through two stack
// aggregates instead of individual arguments: tracked (AS10) values go through
// an array-of-AS10 alloca (which the caller's LateLowerGCFrame turns into GC
// frame slots, so every intermediate state is properly rooted; the frame is
// zero-initialized at push, so slots written only inside the callee scan as
// null until then) and untracked values through an ordinary struct alloca.
// Derived and Mixed inputs remain direct arguments, as do uses not dominated
// by the boundary (e.g. on cold exit paths) which stay ordinary CodeExtractor
// outputs.
//
// Values whose escape is an incoming edge of an exit-target PHI need special
// handling: such a use "happens" at the end of the incoming block (inside the
// region, cf. useBlock), so the use-site rewrite below never sees it, and
// left alone CodeExtractor would marshal the value a second time through a
// scalar alloca of its own — on branchy regions that duplicates the entire
// output interface. Instead the phi itself is demoted into the aggregate
// (one slot per phi, cf. DemotePHIToAggregateSlot). This applies to every
// exit target of the region — the designated boundary and any additional
// exits from reconvergence-failure cuts, which sit on hot paths. Exit
// targets that also merge paths the region does not own (mixed targets,
// e.g. shared joins or throw blocks) keep their phis: demotion would plant
// stores on the foreign edges. Their region-side edges are split instead,
// which turns the crossing phi uses into ordinary external uses served by
// a reload in the caller-side edge block — no cost is added to the foreign
// paths, and nothing is left for CodeExtractor to marshal.
// Tracked INPUT spill slots are dead once their region returns, so sibling
// regions of one function can share a single buffer (created at the maximum
// size seen so far; an occasional larger region allocates a bigger one and
// later regions reuse that). Outputs stay per-region: they remain live from
// the region's return until their last caller-side reload, which commonly
// overlaps later regions.
struct SharedSpillState {
    AllocaInst *Buf = nullptr;
    unsigned Cap = 0;
};

static void spillInterface(Function &F, Region &R, DominatorTree &DT,
                           const SmallPtrSetImpl<BasicBlock *> &Owned,
                           const SetVector<Value *> &Inputs,
                           const SetVector<Value *> &Outputs,
                           SharedSpillState &SS) JL_NOTSAFEPOINT
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
                // A pointer to a caller alloca (e.g. a sibling region's spill
                // buffer threading through a group interface) stays a direct
                // argument: spilling the ADDRESS into the aggregate is an
                // escape that would defeat alias analysis for the buffer
                // itself.
                if (isa<AllocaInst>(V->stripPointerCasts()))
                    break;
                if (V->getType()->isFirstClassType() && V->getType()->isSized())
                    UIn.push_back(V);
                break;
            default:
                break;
            }
        }
    }
    SmallVector<PHINode *, 8> TPhis, UPhis;
    SmallPtrSet<PHINode *, 8> DemoteSet;
    if (Boundary && !SplitNoOutputSpill) {
        // Every block outside the region that a region block branches to: the
        // designated boundary plus any extra exits of multi-exit cuts.
        SmallSetVector<BasicBlock *, 8> ExitTargets;
        for (BasicBlock *BB : R.Blocks)
            for (BasicBlock *S : successors(BB))
                if (!R.Set.count(S))
                    ExitTargets.insert(S);
        for (BasicBlock *T : ExitTargets) {
            // Does any phi of T carry a region value across a region edge?
            bool Crossing = false;
            for (PHINode &PN : T->phis()) {
                for (unsigned i = 0, e = PN.getNumIncomingValues(); i != e; i++) {
                    auto *II = dyn_cast<Instruction>(PN.getIncomingValue(i));
                    if (II && R.Set.count(II->getParent()) &&
                        R.Set.count(PN.getIncomingBlock(i))) {
                        Crossing = true;
                        break;
                    }
                }
                if (Crossing)
                    break;
            }
            if (!Crossing)
                continue;
            // A phi's incoming block list is its parent's predecessor list,
            // so "fed entirely from inside the region" is a per-block
            // property.
            bool AllInterior = true;
            for (BasicBlock *P : predecessors(T)) {
                if (!R.Set.count(P)) {
                    AllInterior = false;
                    break;
                }
            }
            if (!AllInterior) {
                // Mixed target: its phis also merge paths the region does not
                // own, so they must survive, and demoting one would plant
                // stores on those foreign edges. Normalize instead: split
                // each region-side edge, so the phis' incoming blocks become
                // the caller-side edge blocks and the crossing uses turn into
                // ordinary external uses, which the slot rewrite below serves
                // with a load in the edge block — executed only when that
                // edge is taken, and free for every foreign path.
                SmallSetVector<BasicBlock *, 4> InteriorPreds;
                for (BasicBlock *P : predecessors(T))
                    if (R.Set.count(P))
                        InteriorPreds.insert(P);
                for (BasicBlock *P : InteriorPreds)
                    SplitEdge(P, T, &DT, nullptr, nullptr,
                              P->getName() + ".exit");
                continue;
            }
            for (PHINode &PN : T->phis()) {
                bool PNCrossing = false;
                for (Value *IV : PN.incoming_values()) {
                    auto *II = dyn_cast<Instruction>(IV);
                    if (II && R.Set.count(II->getParent())) {
                        PNCrossing = true;
                        break;
                    }
                }
                if (!PNCrossing)
                    continue;
                switch (classifyType(PN.getType())) {
                case ValKind::Tracked:
                    TPhis.push_back(&PN);
                    DemoteSet.insert(&PN);
                    break;
                case ValKind::Untracked:
                    if (PN.getType()->isFirstClassType() && PN.getType()->isSized()) {
                        UPhis.push_back(&PN);
                        DemoteSet.insert(&PN);
                    }
                    break;
                default:
                    // Regions with escapes of other kinds were rejected or
                    // rematerialized before spilling.
                    break;
                }
            }
        }
        // A value whose only escapes are demoted phis needs no slot of its
        // own: the phi slot's edge stores cover it, and the use-site rewrite
        // below would find nothing to rewrite (leaving a dead store).
        auto escapesBeyondDemotedPhis = [&](Instruction *I) JL_NOTSAFEPOINT {
            for (Use &U : I->uses()) {
                if (auto *PN = dyn_cast<PHINode>(U.getUser());
                    PN && DemoteSet.count(PN))
                    continue;
                if (!R.Set.count(useBlock(U)))
                    return true;
            }
            return false;
        };
        for (Value *V : Outputs) {
            auto *I = cast<Instruction>(V);
            if (!escapesBeyondDemotedPhis(I))
                continue;
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
    if (TIn.empty() && UIn.empty() && TOut.empty() && UOut.empty() &&
        TPhis.empty() && UPhis.empty())
        return;
    static int SpillCount = 0;
    if (SplitSpillMax >= 0 && SpillCount >= SplitSpillMax)
        return;
    SpillCount++;
    if (SplitDebug)
        errs() << "julia-function-splitting: spill #" << SpillCount << " at "
               << Entry->getName() << " TIn=" << TIn.size() << " UIn=" << UIn.size()
               << " TOut=" << TOut.size() << " UOut=" << UOut.size()
               << " TPhi=" << TPhis.size() << " UPhi=" << UPhis.size() << "\n";
    ++RegionsSpilled;

    LLVMContext &Ctx = F.getContext();
    Type *T_prjlvalue = PointerType::get(Ctx, AddressSpace::Tracked);
    IRBuilder<> EB(&F.getEntryBlock(), F.getEntryBlock().begin());
    AllocaInst *TSpillIn = nullptr;
    unsigned NIn = TIn.size();
    if (NIn) {
        if (SS.Buf && SS.Cap >= NIn) {
            TSpillIn = SS.Buf;
        }
        else {
            TSpillIn = EB.CreateAlloca(T_prjlvalue, EB.getInt32(NIn), "gcspill.in");
            TSpillIn->setAlignment(Align(sizeof(void *)));
            SS.Buf = TSpillIn;
            SS.Cap = NIn;
        }
    }
    AllocaInst *TSpillOut = nullptr;
    unsigned NOut = TOut.size() + TPhis.size();
    if (NOut) {
        TSpillOut = EB.CreateAlloca(T_prjlvalue, EB.getInt32(NOut), "gcspill.out");
        TSpillOut->setAlignment(Align(sizeof(void *)));
    }
    StructType *UTy = nullptr;
    AllocaInst *USpill = nullptr;
    if (!UIn.empty() || !UOut.empty() || !UPhis.empty()) {
        SmallVector<Type *, 16> Elts;
        for (Value *V : UIn)
            Elts.push_back(V->getType());
        for (Instruction *I : UOut)
            Elts.push_back(I->getType());
        for (PHINode *PN : UPhis)
            Elts.push_back(PN->getType());
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
                V, FB.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpillIn, TSlot),
                Align(sizeof(void *)));
            auto *Reload = RegionFront.CreateAlignedLoad(
                T_prjlvalue,
                RegionFront.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpillIn, TSlot),
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
    // Lower the escaping values and boundary phis into their aggregate slots.
    // (The aggregate null checks are redundant with the emptiness of the
    // corresponding lists; spelled out for the static analyzer.)
    auto isExternalUse = [&](Use &U) JL_NOTSAFEPOINT {
        return !R.Set.count(useBlock(U));
    };
    if (TSpillOut) {
        unsigned TOutSlot = 0;
        for (Instruction *I : TOut) {
            unsigned Slot = TOutSlot++;
            DemoteRegToAggregateSlot(
                *I, Align(sizeof(void *)),
                [&, Slot](IRBuilder<> &B) JL_NOTSAFEPOINT -> Value * {
                    return B.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpillOut, Slot);
                },
                isExternalUse);
        }
        for (PHINode *PN : TPhis) {
            unsigned Slot = TOutSlot++;
            DemotePHIToAggregateSlot(
                *PN, Align(sizeof(void *)),
                [&, Slot](IRBuilder<> &B) JL_NOTSAFEPOINT -> Value * {
                    return B.CreateConstInBoundsGEP1_32(T_prjlvalue, TSpillOut, Slot);
                });
        }
    }
    if (UTy && USpill) {
        for (Instruction *I : UOut) {
            unsigned Slot = USlot++;
            DemoteRegToAggregateSlot(
                *I, MaybeAlign(),
                [&, Slot](IRBuilder<> &B) JL_NOTSAFEPOINT -> Value * {
                    return B.CreateStructGEP(UTy, USpill, Slot);
                },
                isExternalUse);
        }
        for (PHINode *PN : UPhis) {
            unsigned Slot = USlot++;
            DemotePHIToAggregateSlot(
                *PN, MaybeAlign(),
                [&, Slot](IRBuilder<> &B) JL_NOTSAFEPOINT -> Value * {
                    return B.CreateStructGEP(UTy, USpill, Slot);
                });
        }
    }
}

// Sub-stage accumulators (diagnostics; printed under -julia-split-debug).
static int64_t PrepRematMs, PrepCEMs, PrepIOMs, PrepSpillMs;
// Region-growth outcome counters (reset per function; printed under
// -julia-split-time). "clamp" cuts and growth failures mean the realized
// region sizes diverge from the requested target — never silently.
static int64_t GrowCutTarget, GrowCutSafepoint, GrowCutBlocks, GrowCutClamp, GrowFailBlocks, GrowFailSize, GrowFailNoAdd, GrowMinCutTrim;
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
    // Constant-environment duplication (experiment): chains of invariant/
    // immutable loads and address computation over constant leaves are
    // recomputed inside the region instead of crossing the interface.
    auto isConstChain = [&](Value *V, auto &&self, unsigned Depth) JL_NOTSAFEPOINT -> bool {
        if (isa<Constant>(V))
            return true;
        if (Depth >= 4)
            return false;
        auto *I = dyn_cast<Instruction>(V);
        if (!I || R.Set.count(I->getParent()))
            return false;
        bool CloneOK = isa<GetElementPtrInst>(I) || isa<BitCastInst>(I) ||
                       isa<AddrSpaceCastInst>(I);
        if (!CloneOK)
            if (auto *LI = dyn_cast<LoadInst>(I))
                CloneOK = LI->getMetadata(LLVMContext::MD_invariant_load) != nullptr ||
                          isImmutableManagedLoad(LI);
        if (!CloneOK)
            return false;
        for (Value *Op : I->operands())
            if (!self(Op, self, Depth + 1))
                return false;
        return true;
    };
    std::function<Value *(Value *, BasicBlock::iterator)> cloneAt =
        [&](Value *V, BasicBlock::iterator IP) JL_NOTSAFEPOINT -> Value * {
        if (isa<Constant>(V))
            return V;
        auto *I = cast<Instruction>(V);
        Instruction *C = I->clone();
        C->setName(I->getName() + ".remat");
        C->insertBefore(IP);
        for (Use &Op : C->operands())
            if (!isa<Constant>(Op.get()))
                Op.set(cloneAt(Op.get(), C->getIterator()));
        return C;
    };
    DenseMap<Value *, bool> ChainMemo;
    auto wantsClone = [&](Value *V) JL_NOTSAFEPOINT {
        if (isa<Constant>(V) || !isa<Instruction>(V))
            return false;
        if (R.Set.count(cast<Instruction>(V)->getParent()))
            return false;
        auto It = ChainMemo.find(V);
        if (It != ChainMemo.end())
            return It->second;
        return ChainMemo[V] = isConstChain(V, isConstChain, 0);
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
                    if (wantsClone(V))
                        PN->setIncomingValue(
                            i, cloneAt(V, PN->getIncomingBlock(i)
                                              ->getTerminator()
                                              ->getIterator()));
                    else if (wants(V))
                        PN->setIncomingValue(i, proxyFor(V));
                }
                continue;
            }
            for (Use &U : I.operands()) {
                if (wantsClone(U.get()))
                    U.set(cloneAt(U.get(), I.getIterator()));
                else if (wants(U.get()))
                    U.set(proxyFor(U.get()));
            }
        }
    }
}

// Legality check + interface preparation for one region.
static bool prepareRegion(Function &F, Region &R, DominatorTree &DT,
                          const SmallPtrSetImpl<BasicBlock *> &Owned,
                          DenseMap<Value *, bool> &HighFanout,
                          SharedSpillState &SS,
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
        spillInterface(F, R, DT, Owned, Inputs, Outputs, SS);
    }
    else if (SplitOutputSpillMin && Outputs.size() >= SplitOutputSpillMin) {
        // Narrow interface, but still route the outputs through the aggregate:
        // CodeExtractor's fallback is one scalar output alloca per value, i.e.
        // one pointer argument and one isolated stack slot each, which defeats
        // vectorized marshalling and bloats the call frame. Inputs stay direct
        // (they ride in registers).
        SetVector<Value *> NoInputs;
        spillInterface(F, R, DT, Owned, NoInputs, Outputs, SS);
    }
    PrepSpillMs += msc(P5, now());
    return true;
}

// Whether this caller alloca's address stays under the pass's control: every
// transitive user is a plain load, a store *to* it, a GEP, a memset of it, or
// an argument to a call of an extracted region. Then nothing can write the
// buffer during a region's activation except that region itself (the caller
// -- and any sibling region holding the address -- is suspended while it
// runs).
static bool isNonEscapingParentAlloca(AllocaInst *AI) JL_NOTSAFEPOINT
{
    SmallVector<Value *, 8> Work{AI};
    SmallPtrSet<Value *, 8> Seen;
    while (!Work.empty()) {
        Value *A = Work.pop_back_val();
        if (!Seen.insert(A).second)
            continue;
        for (Use &U : A->uses()) {
            auto *UI = dyn_cast<Instruction>(U.getUser());
            if (!UI)
                return false;
            if (auto *LI = dyn_cast<LoadInst>(UI)) {
                if (!LI->isSimple())
                    return false;
                continue;
            }
            if (auto *SI = dyn_cast<StoreInst>(UI)) {
                if (!SI->isSimple() || SI->getValueOperand() == A)
                    return false;
                continue;
            }
            if (isa<GetElementPtrInst>(UI) || isa<BitCastInst>(UI) ||
                isa<AddrSpaceCastInst>(UI)) {
                Work.push_back(UI);
                continue;
            }
            if (auto *MS = dyn_cast<MemSetInst>(UI)) {
                if (MS->getRawDest() != A)
                    return false;
                continue;
            }
            if (auto *CB = dyn_cast<CallBase>(UI)) {
                Function *Callee = CB->getCalledFunction();
                if (!Callee || !CB->isArgOperand(&U) ||
                    !Callee->hasFnAttribute("julia.split-function"))
                    return false;
                continue;
            }
            return false;
        }
    }
    return true;
}

// Classify a region argument's transitive uses: 0 = unknown user or the
// pointer may be captured, 1 = only reads (simple loads, possibly through
// GEPs), 2 = reads and writes through the pointer but never captures it.
static int classifyArgUses(Argument *P) JL_NOTSAFEPOINT
{
    bool Writes = false, Reads = false;
    SmallVector<Value *, 8> Work{P};
    SmallPtrSet<Value *, 8> Seen;
    while (!Work.empty()) {
        Value *A = Work.pop_back_val();
        if (!Seen.insert(A).second)
            continue;
        for (Use &U : A->uses()) {
            auto *UI = dyn_cast<Instruction>(U.getUser());
            if (!UI)
                return 0;
            if (auto *LI = dyn_cast<LoadInst>(UI)) {
                if (!LI->isSimple())
                    return 0;
                Reads = true;
                continue;
            }
            if (auto *SI = dyn_cast<StoreInst>(UI)) {
                if (!SI->isSimple() || SI->getValueOperand() == A)
                    return 0;
                Writes = true;
                continue;
            }
            if (isa<BitCastInst>(UI) || isa<AddrSpaceCastInst>(UI)) {
                Work.push_back(UI);
                continue;
            }
            if (auto *G = dyn_cast<GetElementPtrInst>(UI);
                G && G->getPointerOperand() == A) {
                Work.push_back(G);
                continue;
            }
            return 0;
        }
    }
    if (!Reads && !Writes)
        return 0; // dead argument: nothing to mark
    return Writes ? 2 : 1;
}

// Conservatively determine whether an outlined function may reach a safepoint
// (and hence needs a pgcstack for its GC frame). Over-approximation only
// wastes one TLS load.
// A call that may reach a GC safepoint (and clobbers registers): the unit in
// which register-allocation cost grows within a block, and the unit of any
// safepoint budget for chunk cutting or region growth.
static bool isSafepointCall(const Instruction &I, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    auto *CI = dyn_cast<CallBase>(&I);
    if (!CI || isa<IntrinsicInst>(CI))
        return false;
    Function *Callee = CI->getCalledFunction();
    if (Callee && (Callee == ctx.gc_loaded_func || Callee == ctx.typeof_func ||
                   Callee == ctx.write_barrier_func || Callee == ctx.pointer_from_objref_func ||
                   Callee == ctx.gcroot_flush_func || Callee == ctx.blackbox_func))
        return false;
    return true;
}

static bool mayReachSafepoint(Function &F, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    for (Instruction &I : instructions(F))
        if (isSafepointCall(I, ctx))
            return true;
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
    // Provenance marker: outlined functions are already at the pass's output
    // granularity, so a later invocation (the pipeline runs this pass twice)
    // must not re-split them — doing so cannot reduce their size, it only
    // wraps the body in a shim and stacks a second marshalling layer onto
    // the same interface (which also corrupts SLP's store-group seeds).
    NewF->addFnAttr("julia.split-function");
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
        // Caller-frame buffers the region only touches through loads and
        // stores (the gcspill buffers, sibling regions' out-buffers, demoted
        // value slots) stay valid in the caller's frame for the region's
        // whole activation: the caller is suspended while the region runs,
        // and a non-escaping alloca cannot be written by anyone else. Mark
        // such arguments captures(none) -- and readonly when the region only
        // reads -- so alias analysis and the lifetime passes can treat the
        // region call as an ordinary use of the buffer instead of an escape.
        for (unsigned i = 0; i < CS->arg_size() && i < NewF->arg_size(); i++) {
            auto *AI = dyn_cast<AllocaInst>(CS->getArgOperand(i)->stripPointerCasts());
            if (!AI || !isNonEscapingParentAlloca(AI))
                continue;
            int K = classifyArgUses(NewF->getArg(i));
            if (K == 0)
                continue;
            CS->addParamAttr(i, Attribute::getWithCaptureInfo(Ctx, CaptureInfo::none()));
            NewF->addParamAttr(i, Attribute::getWithCaptureInfo(Ctx, CaptureInfo::none()));
            if (K != 1)
                continue;
            CS->addParamAttr(i, Attribute::get(Ctx, Attribute::ReadOnly));
            NewF->addParamAttr(i, Attribute::get(Ctx, Attribute::ReadOnly));
        }
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
static void privatizeRootBuffers(Function &F, std::vector<Region> &Leaves,
                                 SmallVectorImpl<WeakTrackingVH> &Sunk) JL_NOTSAFEPOINT
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
                Sunk.push_back(NA);
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
                // After the base (already placed), not at the block front, so
                // the clone stays dominated by its address chain.
                C->insertAfter(cast<Instruction>(Base));
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
//
// Every sunk instruction is recorded in Sunk so that any that end up
// stranded outside an entry block (their region was rejected during
// extraction) can be hoisted back: a non-entry alloca is dynamic and
// re-executes on every visit -- inside a loop that grows the stack
// unboundedly for the whole activation.
static void sinkEntryAllocas(Function &F, std::vector<Region> &Leaves,
                             SmallVectorImpl<WeakTrackingVH> &Sunk) JL_NOTSAFEPOINT
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
            Sunk.push_back(A);
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
            Insts += Info.get(B).Size;
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
            auto [ESize, ESafepoints, EPinned] = Info.get(Entry);
    (void)ESafepoints;
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
                auto [SSize, SSafepoints, SPinned] = Info.get(S);
                (void)SSafepoints;
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
            // Progress-fraction floor (cf. growRegion): a stuck parent is
            // worth forming once it covers at least a quarter of EITHER
            // enabled parent cap — the instruction target or the
            // direct-children budget (2*SplitGroupSize at the full cut).
            // Relative to the caps, never an absolute size.
            bool MinProgress = Insts >= std::max(32u, Target / 4) ||
                               Members.size() >= SplitGroupSize / 2;
            if (CanCut && MinProgress && Members.size() >= 2) {
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
                    auto [CSize, CSafepoints, CPinned] = Info.get(Cand);
                    (void)CSafepoints;
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

// InstCombine's single-use code sinking moves an instruction into its user's
// block (at that block's first insertion point) whenever the two differ.
// Across the straight-line seams this pass leaves behind — chunk cuts and the
// block CodeExtractor replaces a region with — that canonicalization cascades:
// once a dependency chain's tail sinks, its producer becomes single-use-cross-
// block too, so the whole chain relocates one instruction at a time, each
// landing above the previously sunk one. Interleaved independent chains come
// out as consecutive serial runs whose length grows with the chunk size: a
// latency pessimization with no structural limit. Sinking across an
// unconditional seam has no benefit in the first place, so fold the seams
// away instead: Cap bounds the resulting block sizes (region bodies stay
// within the region size ceiling, cf. growRegion's MaxSize).
static void mergeStraightSeams(Function &F, unsigned Cap,
                               const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    // Mirror the cut-side safepoint budget (cf. SplitBlockSafepoints in
    // chunkBlock): without it, folding a region body back together would
    // reassemble exactly the call-dense block the chunking cut apart. The
    // 4x slack mirrors Cap's slack relative to the chunk size and stays far
    // below the measured onset of the per-block register-allocation blowup.
    unsigned SPCap = SplitBlockSafepoints ? 4 * SplitBlockSafepoints : 0;
    auto spCount = [&](BasicBlock *BB) JL_NOTSAFEPOINT {
        unsigned N = 0;
        for (Instruction &I : *BB)
            N += isSafepointCall(I, ctx);
        return N;
    };
    for (BasicBlock &B : make_early_inc_range(F)) {
        BasicBlock *P = B.getUniquePredecessor();
        if (!P || P->getSingleSuccessor() != &B)
            continue;
        if (P->size() + B.size() > Cap)
            continue;
        if (SPCap && spCount(P) + spCount(&B) > SPCap)
            continue;
        MergeBlockIntoPredecessor(&B);
    }
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
    SharedSpillState SS;
    SmallPtrSet<HNode *, 16> Prepared;
    for (HNode &N : Items)
        if (prepareRegion(F, N.R, DT, Owned, HighFanout, SS, ctx))
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
    SmallVector<Function *, 16> Extracted;
    for (HNode &N : Items) {
        Function *NewF = nullptr;
        if (Prepared.count(&N))
            NewF = extractRegion(F, N.R, ctx, CEAC);
        if (NewF)
            Extracted.push_back(NewF);
        if (!N.Kids.empty())
            Sub.push_back({&N, NewF});
    }
    CEDummy->eraseFromParent();
    for (auto &[N, NewF] : Sub)
        processLevel(NewF ? *NewF : F, N->Kids, ctx);
    // Fold the seams InstCombine would otherwise sink dependency chains
    // across (see mergeStraightSeams). Runs after the recursion so that no
    // Region::Blocks list of a child refers to a merged-away block. Region
    // bodies merge wholesale under the cap; in the caller only the region's
    // call block is folded into its feeding predecessor (so call operands
    // stay in the same block as their defs) — remaining residual chunk seams
    // are kept to preserve the block-size bound, and the values crossing
    // them (region output reloads) have no chains behind them to cascade.
    // Merging is block formation: it restores the unit of analysis for
    // block-local passes that cutting fractured, so the cap follows the
    // BLOCK target (the knob budgeting block-local analysis cost), matching
    // the block-relative safepoint half in mergeStraightSeams. Region
    // growth is bounded separately by the region target.
    unsigned Cap = 4 * SplitBlockInsts;
    if (SplitNoSeamMerge)
        return;
    for (Function *NewF : Extracted) {
        for (User *U : NewF->users()) {
            auto *CI = dyn_cast<CallBase>(U);
            if (CI && CI->getCalledFunction() == NewF &&
                CI->getParent()->getParent() == &F) {
                MergeBlockIntoPredecessor(CI->getParent());
                break;
            }
        }
        mergeStraightSeams(*NewF, Cap, ctx);
    }
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
    unsigned C = std::max(16u, SplitBlockInsts.getValue());
    // A block qualifies for cutting on either axis: instruction count or
    // safepoint count (call-dense blocks can be far below the instruction
    // spacing yet far above the safepoint budget).
    bool SafepointsQualify = false;
    if (SplitBlockSafepoints) {
        unsigned SP = 0;
        for (Instruction *I : Insts)
            SP += isSafepointCall(*I, ctx);
        SafepointsQualify = SP >= 2 * SplitBlockSafepoints;
    }
    if (n < 2 * C && !SafepointsQualify)
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
    // Composite cut spacing: each instruction weighs 1 and each safepoint
    // call additionally weighs C/SplitBlockSafepoints, so one chunk's weight
    // budget C admits at most about SplitBlockSafepoints safepoints. Register
    // allocation cost grows superlinearly with the safepoints a single block
    // spans, so call-dense stretches need a finer cut quantum than the
    // instruction spacing alone provides. Cutting is also the finest
    // granularity anything downstream can use: blocks and regions may be
    // sized independently (regions with their own instruction and safepoint
    // budgets), and any such budget is only realizable from whole blocks if
    // the cut quantum respects the denser axis.
    SmallVector<uint64_t, 0> WeightPS(n + 1, 0);
    {
        uint64_t SPW = SplitBlockSafepoints
                           ? std::max<uint64_t>(1, C / SplitBlockSafepoints)
                           : 0;
        uint64_t Acc = 0;
        for (unsigned i = 0; i < n; i++) {
            Acc += 1 + (SPW && isSafepointCall(*Insts[i], ctx) ? SPW : 0);
            WeightPS[i + 1] = Acc;
        }
    }
    auto posAtWeight = [&](uint64_t w) JL_NOTSAFEPOINT -> unsigned {
        return (unsigned)(std::lower_bound(WeightPS.begin(), WeightPS.end(), w) -
                          WeightPS.begin());
    };

    // Pick cuts: mandatory cuts fencing off runs of pinned instructions, and
    // within each straight-line span, greedy min-live-score cuts about every
    // SplitBlockInsts instructions. Tracked values weigh heavier: they cost GC
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
        const uint64_t CW = C; // chunk budget in weight units
        while (WeightPS[e] - WeightPS[q] > CW + CW / 2) {
            unsigned lo = posAtWeight(WeightPS[q] + CW / 2);
            unsigned hi = std::min(posAtWeight(WeightPS[q] + CW + CW / 2), e - 1);
            if (lo > hi)
                lo = hi;
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
// Interface width of every grow-order prefix of R.Blocks, in one linear
// pass. Every prefix was the live region at some point during growth, so any
// of them is a legal place to cut; the width decides which one is cheapest.
// Each SSA value contributes to a prefix's interface over a contiguous
// interval of prefix lengths k (blocks are only appended):
//   input:  def outside the prefix, some use inside  ->  minUse <= k < defPos
//   output: def inside the prefix, some use outside  ->  defPos <= k < maxUse
// so one difference-array accumulation over per-value intervals yields the
// exact width profile in O(instructions + uses) -- no per-candidate rescans.
// Tracked values weigh more than untracked ones (a tracked interface slot is
// a GC frame slot in the caller plus rooting traffic; an untracked one is an
// argument register or spill struct field), and derived values sit between
// (they force rematerialization spines).
static void prefixInterfaceProfile(const SmallVectorImpl<BasicBlock *> &Blocks,
                                   SmallVectorImpl<int> &Width) JL_NOTSAFEPOINT
{
    unsigned N = Blocks.size();
    DenseMap<BasicBlock *, unsigned> Pos;
    for (unsigned i = 0; i < N; i++)
        Pos[Blocks[i]] = i;
    SmallVector<int, 128> D(N + 1, 0);
    auto weightOf = [](Type *T) JL_NOTSAFEPOINT -> int {
        switch (classifyType(T)) {
        case ValKind::Tracked:
            return 3;
        case ValKind::Derived:
            return 2;
        case ValKind::Untracked:
            return T->isFirstClassType() && T->isSized() && !T->isVoidTy() ? 1 : 0;
        default:
            return 0;
        }
    };
    DenseMap<Value *, unsigned> ExtMinUse; // external def -> first use position
    for (unsigned pb = 0; pb < N; pb++) {
        for (Instruction &I : *Blocks[pb]) {
            // Region-internal defs: input while the prefix has a use but not
            // the def; output while it has the def but not every use.
            if (int W = weightOf(I.getType())) {
                unsigned MinPU = ~0u, MaxPU = 0;
                for (User *U : I.users()) {
                    auto It = Pos.find(cast<Instruction>(U)->getParent());
                    unsigned PU = It == Pos.end() ? N : It->second;
                    MinPU = std::min(MinPU, PU);
                    MaxPU = std::max(MaxPU, PU);
                }
                if (MinPU != ~0u) {
                    if (MinPU < pb) { // grow order need not follow dominance
                        D[MinPU] += W;
                        D[pb] -= W;
                    }
                    if (MaxPU > pb) {
                        D[pb] += W;
                        D[std::min(MaxPU, N)] -= W;
                    }
                }
            }
            // External defs referenced from inside: input from first use on.
            for (Value *Op : I.operands()) {
                if (isa<Constant>(Op) || isa<BasicBlock>(Op) ||
                    isa<MetadataAsValue>(Op))
                    continue;
                if (auto *OpI = dyn_cast<Instruction>(Op);
                    OpI && Pos.count(OpI->getParent()))
                    continue; // internal def: handled above
                if (!isa<Instruction>(Op) && !isa<Argument>(Op))
                    continue;
                if (int W = weightOf(Op->getType()); W) {
                    auto [It, New] = ExtMinUse.try_emplace(Op, pb);
                    if (!New)
                        It->second = std::min(It->second, pb);
                }
            }
        }
    }
    for (auto &KV : ExtMinUse) {
        int W = weightOf(KV.first->getType());
        D[KV.second] += W;
        // an external input stays an input for every longer prefix
    }
    Width.assign(N, 0);
    int Acc = 0;
    for (unsigned k = 0; k < N; k++) {
        Acc += D[k];
        Width[k] = Acc;
    }
}

static bool growRegion(BasicBlock *Entry, unsigned Target, BlockInfoCache &Info,
                       const SmallPtrSetImpl<BasicBlock *> &Assigned,
                       const DenseMap<BasicBlock *, unsigned> &RPOIndex,
                       Region &R) JL_NOTSAFEPOINT
{
    auto [ESize, ESafepoints, EPinned] = Info.get(Entry);
    (void)ESafepoints;
    if (EPinned || isa<ReturnInst>(Entry->getTerminator()))
        return false;
    unsigned MaxSize = 4 * Target;
    const unsigned MaxBlocks = std::max(16u, SplitMaxRegionBlocks.getValue());

    R.Blocks.push_back(Entry);
    R.Set.insert(Entry);
    unsigned Insts = ESize;
    unsigned Safepoints = ESafepoints;
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
    // One record per grow step (index = R.Blocks.size()-1 at that step):
    // whether that prefix was a legal cut, its boundary, and its cap fills.
    // Consumed by the min-cut selection when a cap forces a cut.
    struct GrowStep {
        BasicBlock *Cand;
        bool CanCut;
        bool CandFull;
        unsigned Insts;
        unsigned Safepoints;
    };
    SmallVector<GrowStep, 64> Steps;
    // Choose the cut among the recorded grow prefixes: the narrowest live
    // interface among eligible ones, preferring the longest prefix on ties;
    // trims the region (and its stats) down to the chosen prefix. The final
    // prefix is always eligible, so this never loses to cutting exactly
    // where growth stopped, on the width metric.
    auto minCutSelect = [&](function_ref<bool(const GrowStep &, unsigned)> Eligible)
        JL_NOTSAFEPOINT -> unsigned {
        unsigned BestK = Steps.size() - 1;
        if (SplitMinCutWindow) {
            SmallVector<int, 128> Width;
            prefixInterfaceProfile(R.Blocks, Width);
            for (unsigned k = 0; k + 1 < Steps.size(); k++) {
                if (!Steps[k].CanCut || !Eligible(Steps[k], k))
                    continue;
                if (Width[k] < Width[BestK] ||
                    (Width[k] == Width[BestK] && k > BestK))
                    BestK = k;
            }
            if (BestK + 1 < R.Blocks.size()) {
                GrowMinCutTrim += R.Blocks.size() - (BestK + 1);
                for (unsigned i = BestK + 1; i < R.Blocks.size(); i++)
                    R.Set.erase(R.Blocks[i]);
                R.Blocks.truncate(BestK + 1);
            }
        }
        R.Boundary = Steps[BestK].Cand;
        R.BoundaryDominated = Steps[BestK].CandFull;
        R.Insts = Steps[BestK].Insts;
        return BestK;
    };
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
            }
            if (!Full)
                continue; // can't add yet: some predecessors outside the group
            auto [SSize, SSafepoints, SPinned] = Info.get(S);
                (void)SSafepoints;
            if (SPinned || isa<ReturnInst>(S->getTerminator()))
                continue; // may act as a boundary, but must stay in the caller
            unsigned Idx = RPOIndex.lookup(S);
            if (!Add || Idx < AddIdx) {
                Add = S;
                AddIdx = Idx;
            }
        }
        bool CanCut = Cand != nullptr && Pending == 0;
        assert(Steps.size() + 1 == R.Blocks.size());
        Steps.push_back({Cand, CanCut, CandFull, Insts, Safepoints});
        // Dual cap: cut at the instruction target OR the safepoint budget,
        // whichever fills first. Per-region compile cost on call-dense code
        // is superlinear in the safepoints spanned (MachineCSE, GreedyRA),
        // so the safepoint axis must bound regions even when the instruction
        // target is large (the call-free case, where boundaries are the cost
        // and regions should grow).
        bool SPFull = SplitRegionSafepoints && Safepoints >= SplitRegionSafepoints;
        // Third cap alongside the instruction target and safepoint budget: bound the
        // block span. GVN's non-local memdep walk PHI-translates each load across the
        // region's blocks, so the CFG-walk compile cost grows as instructions x blocks
        // and branchy block-dense code needs a block bound even at a large inst target.
        bool BlocksFull = SplitRegionBlocks && R.Blocks.size() >= SplitRegionBlocks;
        if (CanCut && (Insts >= Target || SPFull || BlocksFull)) {
            if (Insts >= Target)
                GrowCutTarget++;
            else if (SPFull)
                GrowCutSafepoint++;
            else
                GrowCutBlocks++;
            // Eligible prefixes hold at least 1/window of the final fill on
            // the axis that forced this cut.
            auto fill = [&](const GrowStep &S, unsigned k) JL_NOTSAFEPOINT {
                if (Insts >= Target)
                    return S.Insts;
                if (SPFull)
                    return S.Safepoints;
                return k + 1; // block count
            };
            unsigned Floor = fill(Steps.back(), Steps.size() - 1) /
                             std::max(1u, SplitMinCutWindow.getValue());
            minCutSelect([&](const GrowStep &S, unsigned k) JL_NOTSAFEPOINT {
                return fill(S, k) >= Floor;
            });
            return true;
        }
        bool SPOver = SplitRegionSafepoints &&
                      Safepoints >= 4 * SplitRegionSafepoints;
        bool BlocksOver = SplitRegionBlocks &&
                          R.Blocks.size() >= 4 * SplitRegionBlocks;
        if (!Add || Insts >= MaxSize || SPOver || BlocksOver ||
            R.Blocks.size() >= MaxBlocks) {
            // Progress-fraction floor for stuck growth: a stuck region is worth
            // extracting once it has covered at least a quarter of ANY enabled
            // cap. Each cap defines a cost regime, and a quarter of one means
            // the extraction removes a meaningful share of the surface that cap
            // exists to bound, with the same interface-amortization ratio a
            // full-size region gets. Purely relative to the configured targets:
            // an adverse CFG can at worst quadruple the region count the caps
            // themselves would produce, never fragment into arbitrarily many
            // tiny extractions.
            bool MinProgress =
                Insts >= std::max(16u, Target / 4) ||
                (SplitRegionSafepoints &&
                 Safepoints >= SplitRegionSafepoints / 4) ||
                (SplitRegionBlocks && R.Blocks.size() >= SplitRegionBlocks / 4);
            // When growth stopped against a clamp (rather than getting stuck),
            // any legal cut beats forming no region at all: with the floor
            // unreachable inside the clamp, insisting on it made oversized
            // targets silently no-op on fine-grained CFGs.
            bool Clamped = Insts >= MaxSize || SPOver || BlocksOver ||
                           R.Blocks.size() >= MaxBlocks;
            if (CanCut && (MinProgress || Clamped)) {
                GrowCutClamp++;
                // Same progress floor per prefix; when even the end lacks
                // it (pure clamp), any legal prefix beats forming nothing.
                auto stepProgress = [&](const GrowStep &S, unsigned k) JL_NOTSAFEPOINT {
                    return S.Insts >= std::max(16u, Target / 4) ||
                           (SplitRegionSafepoints &&
                            S.Safepoints >= SplitRegionSafepoints / 4) ||
                           (SplitRegionBlocks && k + 1 >= SplitRegionBlocks / 4);
                };
                minCutSelect([&](const GrowStep &S, unsigned k) JL_NOTSAFEPOINT {
                    return !MinProgress || stepProgress(S, k);
                });
                return true;
            }
            // Loop headers can only be entered as debt: admit the candidate
            // when its unabsorbed predecessors are all retreating edges (loop
            // backedges); the debt clears once the loop body is inside.
            if (Add == nullptr && Cand && Insts < MaxSize && !SPOver &&
                !BlocksOver && R.Blocks.size() < MaxBlocks) {
                auto [CSize, CSafepoints, CPinned] = Info.get(Cand);
                    (void)CSafepoints;
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
                    Insts += Info.get(Cand).Size;
                    Safepoints += Info.get(Cand).Safepoints;
                    continue;
                }
            }
            if (R.Blocks.size() >= MaxBlocks)
                GrowFailBlocks++;
            else if (Insts >= MaxSize)
                GrowFailSize++;
            else
                GrowFailNoAdd++;
            // One line per abandoned region so threshold studies can histogram
            // how large stuck growth actually gets (offline) — the CFG's join
            // density, not our caps, bounds these.
            if (SplitDebug || SplitTime)
                errs() << "julia-function-splitting: growfail"
                       << (R.Blocks.size() >= MaxBlocks ? " maxblocks"
                           : Insts >= MaxSize           ? " maxsize"
                           : BlocksOver                 ? " blocksover"
                           : SPOver                     ? " spover"
                                                        : " stuck")
                       << " insts=" << Insts << " blocks=" << R.Blocks.size()
                       << " safepoints=" << Safepoints
                       << " cancut=" << (CanCut ? 1 : 0) << "\n";
            return false;
        }
        addBlock(Add);
        Insts += Info.get(Add).Size;
        Safepoints += Info.get(Add).Safepoints;
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
    unsigned C = regionSizeTarget();
    // Seeding note: the maximal single-entry region reachable from a seed is
    // exactly the seed's dominator subtree (the Full-frontier growth below
    // converges to it), so dominator-subtree weights would be a sound upper
    // bound for pre-filtering doomed seeds and ordering the rest. Measured:
    // the DomTree + weights cost MORE than the doomed micro-attempts
    // they avoid (tiny frontiers die fast), and heavy-first ordering forms
    // byte-identical regions (both orders are topological on the dominator
    // tree; dominance-independent seeds cannot interact). So the simple scan
    // below is deliberate; boundary continuations (StartQ) drive the common
    // tiling path and the RPO fallback sweeps whatever remains.
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

// Cut every oversized basic block in F down toward the block-size target.
// This is the block-splitting half of the pass, factored out from
// splitFunction so it can also run standalone as BasicBlockSplittingPass.
// It is purely local (splitBasicBlock inserts unconditional-branch seams;
// SSA values cross via dominance) — no region growth, no outlining, no
// interface marshalling — so it is cheap and safe to re-run anywhere in the
// pipeline. The motivating use is right before a size-sensitive per-block
// pass (e.g. SLP) whose input the CFG simplifier would otherwise have
// re-merged back into one oversized block.
static bool splitOversizedBlocks(Function &F, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    if (!SplitBlockThreshold)
        return false;
    SmallVector<BasicBlock *, 4> Oversized;
    for (BasicBlock &BB : F)
        if (BB.size() > SplitBlockThreshold)
            Oversized.push_back(&BB);
    bool Changed = false;
    for (BasicBlock *BB : Oversized)
        Changed |= chunkBlock(F, *BB, ctx);
    return Changed;
}

static bool splitFunction(Function &F, const JuliaPassContext &ctx) JL_NOTSAFEPOINT
{
    // The trigger statistics come from the same per-block analysis region
    // formation runs on (BlockInfoCache), so this scan doubles as the cache
    // warm-up: qualifying functions pay ONE walk total instead of a trigger
    // walk plus a formation walk. It also prices the safepoint and block axes
    // so that outlining profitability can be delegated to the region caps
    // below instead of a shape-blind instruction threshold.
    BlockInfoCache Info(ctx);
    uint64_t TotalInsts = 0, TotalSafepoints = 0, NumBlocks = 0, MaxBlock = 0;
    for (BasicBlock &BB : F) {
        auto [Size, Safepoints, Pinned] = Info.get(&BB);
        (void)Pinned;
        NumBlocks++;
        TotalInsts += Size;
        TotalSafepoints += Safepoints;
        MaxBlock = std::max<uint64_t>(MaxBlock, Size);
    }
    bool BigBlocks = SplitBlockThreshold && MaxBlock > SplitBlockThreshold;
    bool Qualifies = BigBlocks || (SplitFunctionThreshold &&
                                   TotalInsts > SplitFunctionThreshold);
    if (!Qualifies)
        return false;
    bool Changed = false;
    auto now = []() JL_NOTSAFEPOINT { return std::chrono::steady_clock::now(); };
    auto ms = [](auto a, auto b) JL_NOTSAFEPOINT {
        return std::chrono::duration_cast<std::chrono::milliseconds>(b - a).count();
    };
    auto T0 = now();
    GrowCutTarget = GrowCutSafepoint = GrowCutBlocks = GrowCutClamp = GrowFailBlocks = GrowFailSize = GrowFailNoAdd = GrowMinCutTrim = 0;
    IfaceIn = IfaceOut = IfaceInMax = IfaceOutMax = IfaceExits = IfaceCalls = 0;
    if (BigBlocks) {
        bool Chunked = splitOversizedBlocks(F, ctx);
        Changed |= Chunked;
        if (Chunked)
            Info.invalidateSizes();
    }
    auto T1 = now();
    // Outline only when the function exceeds at least one full region cap.
    // The caps ARE the per-function cost models (instructions = general,
    // safepoints = register allocation, blocks = the CFG-walk passes such as
    // GVN's non-local memory-dependency analysis): a function already under
    // every enabled cap satisfies every bound the caps exist to enforce, so
    // no extraction can improve anything and outlining would only add
    // interface marshalling and a boundary call. This also closes the
    // whole-body wart: previously a sub-cap function whose growth stalled at
    // the return could be extracted essentially whole into a same-sized
    // region, paying the interface for zero compile benefit. (Counts are from
    // the pre-chunking scan: chunking only adds ~TotalInsts/BlockInsts seam
    // blocks, which cannot flip a sub-cap function over the block cap unless
    // it already exceeds the instruction cap.)
    // The entry factor gates only the safepoint and block axes: those caps
    // (512) trigger on medium functions whose unsplit compilation is still
    // cheap, where outlining pays the flat per-region stack tax over too
    // little extracted mass. The instruction target is already sized for
    // the workloads whose compile time is the point of this pass, so it
    // gates at 1x regardless.
    unsigned EF = std::max(1u, SplitEntryFactor.getValue());
    bool ExceedsAnyCap =
        TotalInsts > regionSizeTarget() ||
        (SplitRegionSafepoints && TotalSafepoints > (uint64_t)EF * SplitRegionSafepoints) ||
        (SplitRegionBlocks && NumBlocks > (uint64_t)EF * SplitRegionBlocks);
    if (SplitDebug || SplitTime)
        errs() << "julia-function-splitting: " << F.getName()
               << ": totals insts=" << TotalInsts
               << " safepoints=" << TotalSafepoints << " blocks=" << NumBlocks
               << (ExceedsAnyCap ? " (outlining)" : " (under entry gate)")
               << "\n";
    if (!ExceedsAnyCap)
        return Changed;
    // Codegen zero-initializes its single-slot GC root allocas with a memset,
    // which SROA cannot rewrite for non-integral pointer types (rebuilding
    // the value from bytes would need inttoptr), so these slots reach this
    // pass unpromoted even though mem2reg could otherwise dissolve them.
    // Left in memory, every slot referenced by more than one region becomes
    // a pointer argument: escaped for the rest of the pipeline, pinned to a
    // dedicated GC frame slot in the caller, and re-loaded by every region
    // that reads it. Promote them here instead -- rewrite each full-cover
    // zero memset into an equivalent null store (zero bits are null in the
    // tracked address space) and run mem2reg -- so boundary-crossing values
    // ride the interface as SSA and everything else stays in registers.
    {
        const DataLayout &DL = F.getParent()->getDataLayout();
        SmallVector<AllocaInst *, 64> Promotable;
        SmallVector<MemSetInst *, 64> Zeros;
        for (Instruction &I : F.getEntryBlock()) {
            auto *AI = dyn_cast<AllocaInst>(&I);
            if (!AI || AI->isArrayAllocation())
                continue;
            Type *ElT = AI->getAllocatedType();
            if (classifyType(ElT) != ValKind::Tracked)
                continue;
            uint64_t Size = DL.getTypeAllocSize(ElT);
            bool OK = true;
            SmallVector<MemSetInst *, 2> MSes;
            for (User *U : AI->users()) {
                if (auto *LI = dyn_cast<LoadInst>(U);
                    LI && LI->isSimple() && LI->getType() == ElT)
                    continue;
                if (auto *SI = dyn_cast<StoreInst>(U);
                    SI && SI->isSimple() && SI->getPointerOperand() == AI &&
                    SI->getValueOperand()->getType() == ElT)
                    continue;
                auto *MS = dyn_cast<MemSetInst>(U);
                if (MS && !MS->isVolatile() && MS->getRawDest() == AI &&
                    isa<ConstantInt>(MS->getValue()) &&
                    cast<ConstantInt>(MS->getValue())->isZero() &&
                    isa<ConstantInt>(MS->getLength()) &&
                    cast<ConstantInt>(MS->getLength())->getZExtValue() == Size) {
                    MSes.push_back(MS);
                    continue;
                }
                OK = false;
                break;
            }
            if (!OK)
                continue;
            for (MemSetInst *MS : MSes) {
                IRBuilder<> B(MS);
                B.CreateAlignedStore(Constant::getNullValue(ElT), AI, AI->getAlign());
                Zeros.push_back(MS);
            }
            Promotable.push_back(AI);
        }
        for (MemSetInst *MS : Zeros)
            MS->eraseFromParent();
        Promotable.erase(std::remove_if(Promotable.begin(), Promotable.end(),
                                        [](AllocaInst *AI) JL_NOTSAFEPOINT {
                                            return !isAllocaPromotable(AI);
                                        }),
                         Promotable.end());
        if (!Promotable.empty()) {
            DominatorTree DT(F);
            PromoteMemToReg(Promotable, DT);
            Info.invalidateSizes();
        }
    }
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
        errs() << " cuts(target/sp/blocks/clamp)=" << GrowCutTarget << "/"
               << GrowCutSafepoint << "/" << GrowCutBlocks << "/" << GrowCutClamp
               << " growfail(blocks/size/stuck)=" << GrowFailBlocks << "/"
               << GrowFailSize << "/" << GrowFailNoAdd
               << " mincut-trimmed-blocks=" << GrowMinCutTrim << "\n";
    }
    if (Regions.empty())
        return Changed;
    SmallVector<WeakTrackingVH, 64> SunkAllocas;
    privatizeRootBuffers(F, Regions, SunkAllocas);
    sinkEntryAllocas(F, Regions, SunkAllocas);
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
    unsigned LevelTarget = regionSizeTarget();
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
    // Hoist back any sunk instruction stranded outside an entry block: its
    // region was rejected during extraction, so the sunk alloca now
    // re-executes on every visit of its block. A non-entry alloca is a
    // dynamic alloca; inside a loop it grows the stack on every iteration
    // for the rest of the activation. Successful extractions already
    // re-anchored their allocas in the new function's entry (see
    // extractRegion). Reverse iteration with insertion at the entry's front
    // restores the original recorded order (allocas ahead of the address
    // computations rooted at them).
    for (WeakTrackingVH &VH : llvm::reverse(SunkAllocas)) {
        auto *I = dyn_cast_or_null<Instruction>((Value *)VH);
        if (!I)
            continue;
        BasicBlock *BB = I->getParent();
        if (BB->isEntryBlock())
            continue;
        I->moveBefore(BB->getParent()->getEntryBlock().getFirstInsertionPt());
    }
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


} // anonymous namespace

PreservedAnalyses FunctionSplittingPass::run(Module &M, ModuleAnalysisManager &AM)
{
    if (SplitBlockThreshold == 0 && SplitFunctionThreshold == 0)
        return PreservedAnalyses::all();
    JuliaPassContext ctx;
    ctx.initFunctions(M);
    // Snapshot the worklist: extraction adds new (already small) functions.
    // Functions this pass outlined earlier (same or a previous invocation)
    // carry "julia.split-function" and are skipped: they are already within the
    // size contract, so re-splitting them cannot reduce anything (see the
    // marker in extractRegion). The residual original functions are NOT
    // skipped — a later invocation runs on cleaner IR (post-mem2reg) and can
    // extract regions whose growth previously failed, which is genuine
    // reduction of not-yet-outlined content.
    SmallVector<Function *, 16> Work;
    for (Function &F : M)
        if (!F.isDeclaration() && !F.hasFnAttribute(Attribute::OptimizeNone) &&
            !F.hasFnAttribute("julia.split-function"))
            Work.push_back(&F);
    bool Changed = false;
    for (Function *F : Work)
        Changed |= splitFunction(*F, ctx);
    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

// Block-splitting only: cut oversized basic blocks down to the block-size
// target, without any region outlining. Unlike FunctionSplittingPass this
// runs on every function (including ones outlined earlier) since the point
// is to bound basic-block size for a downstream per-block pass, and it is a
// function pass so it can be scheduled inside a function pass manager
// immediately before that pass (e.g. SLP), where the CFG simplifier can no
// longer re-merge the cuts before the consumer sees them.
PreservedAnalyses BasicBlockSplittingPass::run(Function &F, FunctionAnalysisManager &AM) JL_NOTSAFEPOINT
{
    if (SplitBlockThreshold == 0 || F.isDeclaration() ||
        F.hasFnAttribute(Attribute::OptimizeNone))
        return PreservedAnalyses::all();
    JuliaPassContext ctx;
    ctx.initFunctions(*F.getParent());
    bool Changed = splitOversizedBlocks(F, ctx);
    return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
