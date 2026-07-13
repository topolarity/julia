// This file is a part of Julia. License is MIT: https://julialang.org/license
//
// PreciseLifetimeEnds: insert lifetime.end markers for private stack buffers
// from real dataflow liveness.
//
// Julia codegen emits lifetime.start for its stack temporaries but no ends:
// a temporary's last *memory* access is not derivable from Julia-IR liveness
// at emission time. Without ends, StackColoring's forward may-liveness keeps
// every buffer live from its first use to function exit, so buffers used in
// sequence (straight-line code, loop bodies) or across loop back edges all
// appear to interfere and their frame slots never merge (see
// gcframe-wip/shapes.jl in the development branch for measurements).
//
// By this point in the pipeline every read of an analyzable buffer is an
// ordinary visible instruction, so precise ends are computable: READS
// generate liveness backward, FULL CLOBBERS (the lifetime.start, whole-size
// stores/memsets, sret call operands) kill it, and lifetime.end belongs
// exactly where liveness is dead.
//
// Buffers whose address flows into a pointer phi or select (e.g. produced by
// SimplifyCFG sinking the identical edge copies of a memory phi, or by
// union-result selection) are handled through FORWARDERS: a read through the
// phi'd pointer is a read of whichever input buffer arrived, which the
// dataflow models with SSA-style edge substitution — a phi forwarder has its
// own liveness bit that converts into the matching input's bit when
// propagating into each predecessor, exactly like phi-value liveness in any
// SSA liveness analysis. Select forwarders have no edges to split on, so
// their reads conservatively generate all inputs (the union). This recovers
// bounded lifetimes for sunk/selected buffers without rewriting the IR; the
// only precision left on the table vs. un-sinking is that the entangled
// buffers cannot merge with each other (markers are path-insensitive), only
// with everything else.
//
// Soundness contract for every inserted end: no read reachable from the end
// observes bytes written before it, except through a full clobber. In
// addition, because inserting two or more static ends flips the slot into
// StackColoring's marker-driven "conservative" mode (PR27903), the markers
// must then be complete: every use of the buffer must lie within the static
// [start -> ends] region. Both are guaranteed by the admission rule below:
// no use of the candidate (including reads through forwarders that may carry
// it) may be forward-reachable from an inserted end without first passing
// the candidate's lifetime.start. Loops satisfy this (re-reaching the next
// iteration's uses passes the in-loop start); trailing dead stores and
// region re-entry (a clobber restarting liveness after a dead gap, which in
// conservative mode could silently overwrite a merged neighbor's live slot)
// are rejected by it.
//
// This pass must run after the last mid-level DSE-like pass: lifetime.end is
// a kill for DSE, and while any store made dead by a correct end is genuinely
// dead, keeping the pass in the lowering pipeline removes the safety margin
// dependence. It must also run before LateLowerGCFrame consumes markers'
// consequences downstream (StackColoring).

#include "llvm-version.h"
#include "passes.h"

#include <llvm/ADT/BitVector.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/Statistic.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Support/Debug.h>

#include "julia.h"
#include "llvm-codegen-shared.h"

#define DEBUG_TYPE "precise_lifetime_ends"

using namespace llvm;

STATISTIC(EndsInserted, "Number of lifetime.end markers inserted");
STATISTIC(CandidatesAnalyzed, "Number of analyzable allocas considered");
STATISTIC(CandidatesAdmitted, "Number of allocas that received ends");
STATISTIC(ForwardersAnalyzed, "Number of pointer phis/selects modeled");

namespace {

static bool hasTrackedPointer(Type *T)
{
    if (auto *PT = dyn_cast<PointerType>(T))
        return PT->getAddressSpace() >= AddressSpace::FirstSpecial &&
               PT->getAddressSpace() <= AddressSpace::LastSpecial;
    if (auto *AT = dyn_cast<ArrayType>(T))
        return hasTrackedPointer(AT->getElementType());
    if (auto *VT = dyn_cast<VectorType>(T))
        return hasTrackedPointer(VT->getElementType());
    if (auto *ST = dyn_cast<StructType>(T)) {
        for (Type *E : ST->elements()) {
            if (hasTrackedPointer(E))
                return true;
        }
    }
    return false;
}

struct Event {
    Instruction *I;
    unsigned Idx; // candidate index, or forwarder index when IsFwd
    bool IsFwd = false;
    // A single instruction can carry several roles (e.g. a call reading one
    // operand of the buffer while fully rewriting it through an sret
    // operand); the backward transfer applies Kill then Read, so a combined
    // read+kill instruction leaves the buffer live above it.
    bool Read = false;
    bool Kill = false;
    bool Touch = false; // any other access (partial write): admission only
    bool IsStart = false;
};

struct Candidate {
    AllocaInst *AI;
    uint64_t Size;
    CallInst *Start = nullptr;
    SmallVector<Instruction *, 8> Reads;
    SmallVector<Instruction *, 4> Writes;
    SmallVector<Instruction *, 2> Kills;
};

struct Forwarder {
    Instruction *I; // PHINode or SelectInst
    bool Poisoned = false;
    // (incoming block, incoming pointer); block is null for select arms
    SmallVector<std::pair<BasicBlock *, Value *>, 4> Inputs;
    SmallVector<Instruction *, 4> Reads;
    SmallVector<Instruction *, 2> Touches;
};

struct BlockInfo {
    SmallVector<Event, 8> Events; // sorted by instruction order
    BitVector LiveIn;
    BitVector LiveOut;
};

struct PreciseLifetimeEnds {
    Function &F;
    DominatorTree &DT;
    SmallVector<Candidate, 32> Cands;
    SmallVector<Forwarder, 8> Fwds;
    DenseMap<Value *, unsigned> DerivedCand; // candidate-derived pointers
    DenseMap<Value *, unsigned> DerivedFwd;  // forwarder-derived pointers
    DenseMap<Instruction *, unsigned> FwdIndex;
    DenseMap<const BasicBlock *, BlockInfo> Blocks;
    // Per forwarder: liveness bit (NumCands + k) for phis, -1 for selects.
    SmallVector<int, 8> PhiBit;
    // Per forwarder: bits its reads generate (candidate bits directly, phi
    // bits for phi forwarders, select inputs resolved transitively).
    SmallVector<SmallVector<unsigned, 4>, 8> GenBits;
    // Per forwarder: which candidates may arrive through it (transitive).
    SmallVector<BitVector, 8> Carried;
    // Per candidate: bits whose liveness implies the candidate may be live
    // (its own bit plus the bits of phi forwarders that may carry it).
    SmallVector<SmallVector<unsigned, 4>, 32> CarrierBits;
    // (phi parent, predecessor) -> [(phi bit, replacement bits)]
    DenseMap<std::pair<const BasicBlock *, const BasicBlock *>,
             SmallVector<std::pair<unsigned, SmallVector<unsigned, 4>>, 2>>
        EdgeSubst;

    PreciseLifetimeEnds(Function &F, DominatorTree &DT) JL_NOTSAFEPOINT : F(F), DT(DT) {}
    bool run() JL_NOTSAFEPOINT;
    unsigned getOrCreateFwd(Instruction *I) JL_NOTSAFEPOINT;
    bool analyzeUsers(AllocaInst *AI, uint64_t Size, const DataLayout &DL,
                      Candidate &C, unsigned CandIdx) JL_NOTSAFEPOINT;
    void analyzeForwarder(unsigned FwdIdx) JL_NOTSAFEPOINT;
    void resolveValueBits(Value *V, SmallVectorImpl<unsigned> &Bits) JL_NOTSAFEPOINT;
    void addEvent(Instruction *I, unsigned Idx, bool IsFwd, bool Read, bool Kill,
                  bool Touch, bool IsStart) JL_NOTSAFEPOINT;
    bool admissible(unsigned Cand,
                    ArrayRef<std::pair<Instruction *, BasicBlock *>> Ends)
        JL_NOTSAFEPOINT;
};

unsigned PreciseLifetimeEnds::getOrCreateFwd(Instruction *I)
{
    auto It = FwdIndex.find(I);
    if (It != FwdIndex.end())
        return It->second;
    unsigned Idx = Fwds.size();
    FwdIndex[I] = Idx;
    Forwarder Fwd;
    Fwd.I = I;
    if (auto *PN = dyn_cast<PHINode>(I)) {
        for (unsigned i = 0; i < PN->getNumIncomingValues(); i++)
            Fwd.Inputs.push_back({PN->getIncomingBlock(i), PN->getIncomingValue(i)});
    }
    else {
        auto *SI = cast<SelectInst>(I);
        Fwd.Inputs.push_back({nullptr, SI->getTrueValue()});
        Fwd.Inputs.push_back({nullptr, SI->getFalseValue()});
    }
    Fwds.push_back(std::move(Fwd));
    return Idx;
}

// Walk all users of AI, classifying accesses. Returns false (bail) if any
// user is not fully understood or the address escapes somewhere a forwarder
// cannot model.
bool PreciseLifetimeEnds::analyzeUsers(AllocaInst *AI, uint64_t Size,
                                       const DataLayout &DL, Candidate &C,
                                       unsigned CandIdx)
{
    // (derived pointer, byte offset from the alloca if constant)
    SmallVector<std::pair<Value *, std::optional<int64_t>>, 8> Worklist;
    SmallVector<Value *, 16> Derived;
    SmallPtrSet<Value *, 16> Visited;
    Worklist.push_back({AI, 0});
    Visited.insert(AI);
    Derived.push_back(AI);
    while (!Worklist.empty()) {
        auto [V, Off] = Worklist.pop_back_val();
        for (Use &U : V->uses()) {
            auto *I = dyn_cast<Instruction>(U.getUser());
            if (I == nullptr)
                return false;
            if (auto *GEP = dyn_cast<GetElementPtrInst>(I)) {
                std::optional<int64_t> NewOff;
                APInt APOff(DL.getIndexSizeInBits(GEP->getPointerAddressSpace()), 0);
                if (Off && GEP->accumulateConstantOffset(DL, APOff))
                    NewOff = *Off + APOff.getSExtValue();
                if (Visited.insert(I).second) {
                    Worklist.push_back({I, NewOff});
                    Derived.push_back(I);
                }
                continue;
            }
            if (isa<BitCastInst>(I) || isa<AddrSpaceCastInst>(I)) {
                if (Visited.insert(I).second) {
                    Worklist.push_back({I, Off});
                    Derived.push_back(I);
                }
                continue;
            }
            if (isa<PHINode>(I) || isa<SelectInst>(I)) {
                // The address travels onward; model it as a forwarder. (For
                // selects the pointer is necessarily a data operand: the
                // condition cannot be a pointer.)
                getOrCreateFwd(I);
                continue;
            }
            if (auto *II = dyn_cast<IntrinsicInst>(I)) {
                if (II->getIntrinsicID() == Intrinsic::lifetime_start) {
                    if (C.Start != nullptr)
                        return false; // multiple starts: not our protocol
                    C.Start = cast<CallInst>(II);
                    continue;
                }
                if (II->getIntrinsicID() == Intrinsic::lifetime_end)
                    return false; // ends already managed elsewhere (phi bufs)
                if (auto *MT = dyn_cast<MemTransferInst>(II)) {
                    if (MT->isVolatile())
                        return false;
                    auto *Len = dyn_cast<ConstantInt>(MT->getLength());
                    if (U.getOperandNo() == 0) {
                        if (Len && Off && *Off == 0 && Len->getZExtValue() >= Size)
                            C.Kills.push_back(I);
                        else
                            C.Writes.push_back(I);
                    }
                    else if (U.getOperandNo() == 1) {
                        C.Reads.push_back(I);
                    }
                    else {
                        return false;
                    }
                    continue;
                }
                if (auto *MS = dyn_cast<MemSetInst>(II)) {
                    if (MS->isVolatile() || U.getOperandNo() != 0)
                        return false;
                    auto *Len = dyn_cast<ConstantInt>(MS->getLength());
                    if (Len && Off && *Off == 0 && Len->getZExtValue() >= Size)
                        C.Kills.push_back(I);
                    else
                        C.Writes.push_back(I);
                    continue;
                }
                return false;
            }
            if (auto *LI = dyn_cast<LoadInst>(I)) {
                if (LI->isVolatile())
                    return false;
                C.Reads.push_back(I);
                continue;
            }
            if (auto *SI = dyn_cast<StoreInst>(I)) {
                if (SI->isVolatile())
                    return false;
                if (SI->getValueOperand() == V)
                    return false; // address escapes
                uint64_t StoreSz = DL.getTypeStoreSize(SI->getValueOperand()->getType());
                if (Off && *Off == 0 && StoreSz >= Size)
                    C.Kills.push_back(I);
                else
                    C.Writes.push_back(I);
                continue;
            }
            if (auto *CB = dyn_cast<CallBase>(I)) {
                if (!CB->isArgOperand(&U))
                    return false;
                unsigned ArgNo = CB->getArgOperandNo(&U);
                if (!CB->doesNotCapture(ArgNo))
                    return false;
                if (CB->paramHasAttr(ArgNo, Attribute::StructRet)) {
                    // The callee (re)writes the entire object. Callees do not
                    // read their sret memory's previous contents; padding
                    // bytes it may skip can only be *read* onward, never
                    // corrupt a merged neighbor.
                    C.Kills.push_back(I);
                    continue;
                }
                if (CB->paramHasAttr(ArgNo, Attribute::ReadOnly)) {
                    C.Reads.push_back(I);
                    continue;
                }
                // Writable non-sret argument: may read and write any part.
                C.Reads.push_back(I);
                C.Writes.push_back(I);
                continue;
            }
            return false;
        }
    }
    // Only buffers following codegen's start protocol are eligible.
    if (C.Start == nullptr)
        return false;
    for (Value *V : Derived)
        DerivedCand[V] = CandIdx;
    return true;
}

// Classify a forwarder's users. Poisons the forwarder when a user cannot be
// modeled; chains through further phis/selects and derived pointers.
void PreciseLifetimeEnds::analyzeForwarder(unsigned FwdIdx)
{
    SmallVector<Value *, 8> Worklist{Fwds[FwdIdx].I};
    SmallPtrSet<Value *, 8> Visited;
    Visited.insert(Fwds[FwdIdx].I);
    DerivedFwd[Fwds[FwdIdx].I] = FwdIdx;
    while (!Worklist.empty()) {
        Value *V = Worklist.pop_back_val();
        for (Use &U : V->uses()) {
            auto *I = dyn_cast<Instruction>(U.getUser());
            if (I == nullptr) {
                Fwds[FwdIdx].Poisoned = true;
                return;
            }
            if (isa<GetElementPtrInst>(I) || isa<BitCastInst>(I) ||
                isa<AddrSpaceCastInst>(I)) {
                if (Visited.insert(I).second) {
                    Worklist.push_back(I);
                    DerivedFwd[I] = FwdIdx;
                }
                continue;
            }
            if (isa<PHINode>(I) || isa<SelectInst>(I)) {
                getOrCreateFwd(I); // chain; inputs resolved via DerivedFwd
                continue;
            }
            if (auto *LI = dyn_cast<LoadInst>(I)) {
                if (LI->isVolatile()) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                Fwds[FwdIdx].Reads.push_back(I);
                continue;
            }
            if (auto *SI = dyn_cast<StoreInst>(I)) {
                if (SI->isVolatile() || SI->getValueOperand() == V) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                // A write through the forwarder writes one of the inputs; it
                // never kills, and it counts as a touch for admission.
                Fwds[FwdIdx].Touches.push_back(I);
                continue;
            }
            if (auto *MT = dyn_cast<MemTransferInst>(I)) {
                if (MT->isVolatile()) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                if (U.getOperandNo() == 1)
                    Fwds[FwdIdx].Reads.push_back(I);
                else if (U.getOperandNo() == 0)
                    Fwds[FwdIdx].Touches.push_back(I);
                else {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                continue;
            }
            if (auto *MS = dyn_cast<MemSetInst>(I)) {
                if (MS->isVolatile() || U.getOperandNo() != 0) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                Fwds[FwdIdx].Touches.push_back(I);
                continue;
            }
            if (auto *CB = dyn_cast<CallBase>(I)) {
                if (!CB->isArgOperand(&U)) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                unsigned ArgNo = CB->getArgOperandNo(&U);
                if (!CB->doesNotCapture(ArgNo)) {
                    Fwds[FwdIdx].Poisoned = true;
                    return;
                }
                Fwds[FwdIdx].Reads.push_back(I);
                if (!CB->paramHasAttr(ArgNo, Attribute::ReadOnly))
                    Fwds[FwdIdx].Touches.push_back(I);
                continue;
            }
            Fwds[FwdIdx].Poisoned = true;
            return;
        }
    }
}

// Resolve a forwarder input to liveness bits: candidate bit, phi-forwarder
// bit, or (transitively, via GenBits) a select-forwarder's inputs.
// Unrecognized pointers (heap objects, non-candidate allocas) contribute
// nothing.
void PreciseLifetimeEnds::resolveValueBits(Value *V, SmallVectorImpl<unsigned> &Bits)
{
    auto CIt = DerivedCand.find(V);
    if (CIt != DerivedCand.end()) {
        Bits.push_back(CIt->second);
        return;
    }
    auto FIt = DerivedFwd.find(V);
    if (FIt == DerivedFwd.end())
        return;
    unsigned Fwd = FIt->second;
    if (PhiBit[Fwd] >= 0) {
        Bits.push_back((unsigned)PhiBit[Fwd]);
        return;
    }
    for (unsigned B : GenBits[Fwd])
        Bits.push_back(B);
}

void PreciseLifetimeEnds::addEvent(Instruction *I, unsigned Idx, bool IsFwd,
                                   bool Read, bool Kill, bool Touch, bool IsStart)
{
    auto &BI = Blocks[I->getParent()];
    for (Event &E : BI.Events) {
        if (E.I == I && E.Idx == Idx && E.IsFwd == IsFwd) {
            E.Read |= Read;
            E.Kill |= Kill;
            E.Touch |= Touch;
            E.IsStart |= IsStart;
            return;
        }
    }
    BI.Events.push_back(Event{I, Idx, IsFwd, Read, Kill, Touch, IsStart});
}

// The admission rule: no use of the candidate — including reads/touches
// through forwarders that may carry it — may be forward-reachable from any
// planned end without first passing the candidate's lifetime.start.
bool PreciseLifetimeEnds::admissible(
    unsigned Cand, ArrayRef<std::pair<Instruction *, BasicBlock *>> Ends)
{
    auto matches = [&](const Event &E) JL_NOTSAFEPOINT {
        if (!E.IsFwd)
            return E.Idx == Cand;
        return Carried[E.Idx].test(Cand);
    };
    // Scan a block's (sorted) events starting after `After` (or from the top
    // when null). Returns: 0 = continue into successors, 1 = stop this path
    // (hit the start), -1 = violation.
    auto scanBlock = [&](const BasicBlock *BB, Instruction *After) JL_NOTSAFEPOINT -> int {
        auto It = Blocks.find(BB);
        if (It == Blocks.end())
            return 0;
        for (const Event &E : It->second.Events) {
            if (!matches(E))
                continue;
            if (After != nullptr && (E.I == After || E.I->comesBefore(After)))
                continue;
            if (E.IsStart)
                return 1;
            return -1;
        }
        return 0;
    };
    SmallPtrSet<const BasicBlock *, 16> Visited;
    SmallVector<const BasicBlock *, 16> Worklist;
    for (auto [I, BB] : Ends) {
        if (I != nullptr) {
            int r = scanBlock(I->getParent(), I);
            if (r < 0)
                return false;
            if (r == 0)
                for (const BasicBlock *S : successors(I->getParent()))
                    if (Visited.insert(S).second)
                        Worklist.push_back(S);
        }
        else {
            if (Visited.insert(BB).second)
                Worklist.push_back(BB);
        }
    }
    while (!Worklist.empty()) {
        const BasicBlock *BB = Worklist.pop_back_val();
        int r = scanBlock(BB, nullptr);
        if (r < 0)
            return false;
        if (r != 0)
            continue;
        for (const BasicBlock *S : successors(BB))
            if (Visited.insert(S).second)
                Worklist.push_back(S);
    }
    return true;
}

bool PreciseLifetimeEnds::run()
{
    // Liveness across a returns-twice call is not representable in the CFG.
    for (const Instruction &I : instructions(F)) {
        if (auto *CB = dyn_cast<CallBase>(&I)) {
            if (CB->hasFnAttr(Attribute::ReturnsTwice))
                return false;
        }
    }

    const DataLayout &DL = F.getParent()->getDataLayout();
    for (Instruction &I : F.getEntryBlock()) {
        auto *AI = dyn_cast<AllocaInst>(&I);
        if (AI == nullptr || !AI->isStaticAlloca())
            continue;
        // INVARIANT: never add lifetime markers to GC-visible (tracked)
        // buffers. The GC reads them asynchronously at safepoints — a reader
        // no def-use walk can see — and markers would additionally license
        // LLVM's own StackColoring to merge them, which is unsound for
        // scanned memory (no re-zeroing, undef invention). Their packing
        // belongs exclusively to llvm-late-gc-lowering.
        if (hasTrackedPointer(AI->getAllocatedType()))
            continue;
        auto SizeOpt = AI->getAllocationSize(DL);
        if (!SizeOpt || SizeOpt->isScalable())
            continue;
        Candidate C;
        C.AI = AI;
        C.Size = SizeOpt->getFixedValue();
        if (C.Size == 0 || !analyzeUsers(AI, C.Size, DL, C, Cands.size()))
            continue;
        // The start must dominate every direct access for marker-driven
        // intervals to cover them. (Reads through forwarders are covered by
        // the marker region's may-flow through the forwarding edge instead.)
        bool Dominated = true;
        auto checkDominated = [&](ArrayRef<Instruction *> Users) JL_NOTSAFEPOINT {
            for (Instruction *U : Users) {
                if (!DT.dominates(C.Start, U)) {
                    Dominated = false;
                    break;
                }
            }
        };
        checkDominated(C.Reads);
        checkDominated(C.Writes);
        checkDominated(C.Kills);
        if (!Dominated)
            continue;
        CandidatesAnalyzed++;
        Cands.push_back(std::move(C));
    }
    if (Cands.empty())
        return false;
    unsigned NumCands = Cands.size();

    // Classify forwarder users (this may discover chained forwarders).
    for (unsigned f = 0; f < Fwds.size(); f++) {
        analyzeForwarder(f);
        ForwardersAnalyzed++;
    }

    // Which candidates may each forwarder carry (transitively)?
    Carried.resize(Fwds.size());
    for (auto &BV : Carried)
        BV.resize(NumCands);
    bool CarriedChanged = true;
    while (CarriedChanged) {
        CarriedChanged = false;
        for (unsigned f = 0; f < Fwds.size(); f++) {
            for (auto &[Pred, V] : Fwds[f].Inputs) {
                auto CIt = DerivedCand.find(V);
                if (CIt != DerivedCand.end() && !Carried[f].test(CIt->second)) {
                    Carried[f].set(CIt->second);
                    CarriedChanged = true;
                }
                auto FIt = DerivedFwd.find(V);
                if (FIt != DerivedFwd.end() && FIt->second != f) {
                    BitVector Merged = Carried[f];
                    Merged |= Carried[FIt->second];
                    if (Merged != Carried[f]) {
                        Carried[f] = std::move(Merged);
                        CarriedChanged = true;
                    }
                }
            }
        }
    }

    // Poison propagation: a poisoned forwarder makes every candidate it may
    // carry unanalyzable (some access to it is not modeled).
    BitVector Bailed(NumCands);
    for (unsigned f = 0; f < Fwds.size(); f++) {
        if (Fwds[f].Poisoned)
            Bailed |= Carried[f];
    }

    // Assign liveness bits to phi forwarders; resolve gen sets (two rounds:
    // select chains are acyclic — operands dominate — but may be discovered
    // in any order).
    PhiBit.resize(Fwds.size(), -1);
    unsigned NumBits = NumCands;
    for (unsigned f = 0; f < Fwds.size(); f++) {
        if (isa<PHINode>(Fwds[f].I))
            PhiBit[f] = NumBits++;
    }
    GenBits.resize(Fwds.size());
    for (int round = 0; round < 2; round++) {
        for (unsigned f = 0; f < Fwds.size(); f++) {
            SmallVector<unsigned, 4> Bits;
            if (PhiBit[f] >= 0) {
                Bits.push_back((unsigned)PhiBit[f]);
            }
            else {
                for (auto &[Pred, V] : Fwds[f].Inputs)
                    resolveValueBits(V, Bits);
            }
            std::sort(Bits.begin(), Bits.end());
            Bits.erase(std::unique(Bits.begin(), Bits.end()), Bits.end());
            GenBits[f] = std::move(Bits);
        }
    }
    // Edge substitutions for phi forwarders.
    for (unsigned f = 0; f < Fwds.size(); f++) {
        if (PhiBit[f] < 0)
            continue;
        const BasicBlock *Parent = Fwds[f].I->getParent();
        for (auto &[Pred, V] : Fwds[f].Inputs) {
            SmallVector<unsigned, 4> Bits;
            resolveValueBits(V, Bits);
            EdgeSubst[{Parent, Pred}].push_back({(unsigned)PhiBit[f], std::move(Bits)});
        }
    }
    // Per candidate: bits that may carry it.
    CarrierBits.resize(NumCands);
    for (unsigned c = 0; c < NumCands; c++)
        CarrierBits[c].push_back(c);
    for (unsigned f = 0; f < Fwds.size(); f++) {
        if (PhiBit[f] < 0)
            continue;
        for (unsigned c : Carried[f].set_bits())
            CarrierBits[c].push_back((unsigned)PhiBit[f]);
    }

    // Reposition each start marker tightly: to the nearest common dominator
    // of the buffer's direct accesses, immediately before the earliest access
    // there. Codegen parks some starts in the entry block (the
    // promotion-hazard placement); if such a candidate receives two or more
    // ends it flips to StackColoring's marker-driven mode, where an
    // entry-block start makes the interval span the whole function.
    // Promotion is long finished at this point in the pipeline, so a tight,
    // still-dominating position is equivalent and strictly better. (Between
    // the old and new position the buffer has no accesses, so declaring its
    // contents undef later is harmless. Forwarder reads sit below the phi
    // that the direct accesses feed, so they remain in the marker region's
    // may-flow.)
    for (Candidate &C : Cands) {
        BasicBlock *D = nullptr;
        auto joinBlocks = [&](ArrayRef<Instruction *> Users) JL_NOTSAFEPOINT {
            for (Instruction *U : Users)
                D = D ? DT.findNearestCommonDominator(D, U->getParent()) : U->getParent();
        };
        joinBlocks(C.Reads);
        joinBlocks(C.Writes);
        joinBlocks(C.Kills);
        if (D == nullptr)
            continue; // all accesses flow through forwarders; leave the start
        Instruction *IP = D->getTerminator();
        auto tighten = [&](ArrayRef<Instruction *> Users) JL_NOTSAFEPOINT {
            for (Instruction *U : Users)
                if (U->getParent() == D && U->comesBefore(IP))
                    IP = U;
        };
        tighten(C.Reads);
        tighten(C.Writes);
        tighten(C.Kills);
        if (C.Start != IP && C.Start->getNextNode() != IP)
            C.Start->moveBefore(*IP->getParent(), IP->getIterator());
    }

    // Build per-block event lists.
    for (unsigned c = 0; c < NumCands; c++) {
        Candidate &C = Cands[c];
        addEvent(C.Start, c, false, /*Read*/ false, /*Kill*/ true, false,
                 /*IsStart*/ true);
        for (Instruction *I : C.Reads)
            addEvent(I, c, false, true, false, false, false);
        for (Instruction *I : C.Kills)
            addEvent(I, c, false, false, true, false, false);
        for (Instruction *I : C.Writes)
            addEvent(I, c, false, false, false, true, false);
    }
    for (unsigned f = 0; f < Fwds.size(); f++) {
        if (Fwds[f].Poisoned || Carried[f].none())
            continue;
        for (Instruction *I : Fwds[f].Reads)
            addEvent(I, f, true, true, false, false, false);
        for (Instruction *I : Fwds[f].Touches)
            addEvent(I, f, true, false, false, true, false);
    }
    // Give every block an entry up front so the dataflow never mutates the
    // map (and thereby invalidates references) while iterating.
    for (BasicBlock &BB : F) {
        auto &BI = Blocks[&BB];
        BI.LiveIn.resize(NumBits);
        BI.LiveOut.resize(NumBits);
        std::sort(BI.Events.begin(), BI.Events.end(),
                  [](const Event &A, const Event &B) JL_NOTSAFEPOINT {
                      if (A.I == B.I)
                          return std::make_pair(A.IsFwd, A.Idx) <
                                 std::make_pair(B.IsFwd, B.Idx);
                      return A.I->comesBefore(B.I);
                  });
    }

    // Backward may-liveness: reads generate, kills stop propagation, phi
    // forwarder bits convert to the matching input's bits at each edge.
    bool Changed = true;
    BitVector Live(NumBits);
    BitVector EdgeLive(NumBits);
    while (Changed) {
        Changed = false;
        for (const BasicBlock *BB : post_order(&F)) {
            Live.reset();
            for (const BasicBlock *S : successors(BB)) {
                EdgeLive = Blocks.find(S)->second.LiveIn;
                auto SIt = EdgeSubst.find({S, BB});
                if (SIt != EdgeSubst.end()) {
                    for (auto &[Bit, Repl] : SIt->second) {
                        if (EdgeLive.test(Bit)) {
                            EdgeLive.reset(Bit);
                            for (unsigned R : Repl)
                                EdgeLive.set(R);
                        }
                    }
                }
                Live |= EdgeLive;
            }
            auto &BI = Blocks.find(BB)->second;
            if (Live != BI.LiveOut) {
                BI.LiveOut = Live;
                Changed = true;
            }
            for (auto EIt = BI.Events.rbegin(); EIt != BI.Events.rend(); ++EIt) {
                if (EIt->IsFwd) {
                    if (EIt->Read)
                        for (unsigned B : GenBits[EIt->Idx])
                            Live.set(B);
                }
                else {
                    if (EIt->Kill)
                        Live.reset(EIt->Idx);
                    if (EIt->Read)
                        Live.set(EIt->Idx);
                }
            }
            if (Live != BI.LiveIn) {
                BI.LiveIn = Live;
                Changed = true;
            }
        }
    }

    auto effLive = [&](const BitVector &BV, unsigned c) JL_NOTSAFEPOINT {
        for (unsigned B : CarrierBits[c])
            if (BV.test(B))
                return true;
        return false;
    };

    // Placement.
    bool Inserted = false;
    SmallVector<SmallVector<std::pair<Instruction *, BasicBlock *>, 2>, 32> Plans(NumCands);
    SmallVector<unsigned, 8> ReadOf;
    for (auto &KV : Blocks) {
        const BasicBlock *BB = KV.first;
        BlockInfo &BI = KV.second;
        // An end in a block that never falls through bounds nothing: the
        // block has no successors, so liveness dies with it in every mode.
        // Suppressing these keeps cold-read candidates at a single end,
        // which preserves first-use anchoring; a second end would flip the
        // slot into marker-driven mode.
        bool NoExit = isa<UnreachableInst>(BB->getTerminator());
        // Within-block deaths: a read below which the candidate is dead.
        Live = BI.LiveOut;
        for (auto EIt = BI.Events.rbegin(); EIt != BI.Events.rend(); ++EIt) {
            const Event &E = *EIt;
            if (E.Read && !NoExit) {
                ReadOf.clear();
                if (E.IsFwd) {
                    for (unsigned c : Carried[E.Idx].set_bits())
                        ReadOf.push_back(c);
                }
                else {
                    ReadOf.push_back(E.Idx);
                }
                for (unsigned c : ReadOf) {
                    if (Bailed.test(c) || effLive(Live, c))
                        continue;
                    if (E.I->isTerminator()) {
                        // e.g. an invoke consuming the buffer: the "after"
                        // position is its successors' tops.
                        for (BasicBlock *S : successors(E.I->getParent())) {
                            if (S->getFirstInsertionPt() == S->end()) {
                                Bailed.set(c);
                                break;
                            }
                            Plans[c].push_back({nullptr, S});
                        }
                    }
                    else {
                        Plans[c].push_back({E.I, nullptr});
                    }
                }
            }
            if (E.IsFwd) {
                if (E.Read)
                    for (unsigned B : GenBits[E.Idx])
                        Live.set(B);
            }
            else {
                if (E.Kill)
                    Live.reset(E.Idx);
                if (E.Read)
                    Live.set(E.Idx);
            }
        }
        // Region exits: dead on entry here, live out of some predecessor.
        for (unsigned c = 0; c < NumCands; c++) {
            if (Bailed.test(c) || effLive(BI.LiveIn, c))
                continue;
            bool FromLive = false;
            for (const BasicBlock *P : predecessors(BB)) {
                auto PIt = Blocks.find(P);
                if (PIt != Blocks.end() && effLive(PIt->second.LiveOut, c)) {
                    FromLive = true;
                    break;
                }
            }
            if (!FromLive)
                continue;
            if (isa<UnreachableInst>(BB->getTerminator()))
                continue; // bounds nothing (see above)
            if (BB->getFirstInsertionPt() == BB->end()) {
                Bailed.set(c); // no insertion point (catchswitch)
                continue;
            }
            Plans[c].push_back({nullptr, const_cast<BasicBlock *>(BB)});
        }
    }

    for (unsigned c = 0; c < NumCands; c++) {
        if (Bailed.test(c) || Plans[c].empty())
            continue;
        if (!admissible(c, Plans[c]))
            continue;
        for (auto [I, BB] : Plans[c]) {
            if (I != nullptr) {
                IRBuilder<> Bld(I->getParent(), std::next(I->getIterator()));
                Bld.CreateLifetimeEnd(Cands[c].AI);
            }
            else {
                IRBuilder<> Bld(BB, BB->getFirstInsertionPt());
                Bld.CreateLifetimeEnd(Cands[c].AI);
            }
            EndsInserted++;
        }
        CandidatesAdmitted++;
        Inserted = true;
        LLVM_DEBUG(dbgs() << "precise-lifetime-ends: " << Plans[c].size()
                          << " end(s) for " << *Cands[c].AI << "\n");
    }
    return Inserted;
}

} // namespace

PreservedAnalyses PreciseLifetimeEndsPass::run(Function &F, FunctionAnalysisManager &AM)
{
    auto &DT = AM.getResult<DominatorTreeAnalysis>(F);
    bool Modified = PreciseLifetimeEnds(F, DT).run();
#ifdef JL_VERIFY_PASSES
    assert(!verifyLLVMIR(F));
#endif
    if (Modified)
        return PreservedAnalyses::allInSet<CFGAnalyses>();
    return PreservedAnalyses::all();
}
