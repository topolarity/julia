// This file is a part of Julia. License is MIT: https://julialang.org/license

// This LLVM pass verifies invariants that the intrinsic-lowering section of
// the pipeline (LateLowerGCFrame, FinalLowerGC, LowerPTLS,
// RemoveJuliaAddrspaces) is contracted to establish for machine lowering. It
// runs after that section in verification (JL_VERIFY_PASSES) builds, where
// the GC-invariant verifier can no longer see: those passes run after it and
// their output feeds instruction selection directly.
//
// Checks:
//  * Constant-size allocas live in the entry block. LLVM's staticness test
//    is purely positional (entry block + constant size); an alloca anywhere
//    else is lowered as a dynamic alloca -- a stack-probe and rsp bookkeeping
//    on every visit of its block (unbounded growth if the block is in a
//    loop), var-sized-frame handling for the whole function, and no static
//    frame-index addressing.
//  * No unlowered julia.* runtime intrinsics remain. A call that survives
//    lowering either crashes at link/run time or silently misses its
//    semantics (e.g. an unlowered safepoint).

#include "llvm-version.h"
#include "passes.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/InstVisitor.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Value.h>
#include <llvm/Support/Debug.h>

#include "julia.h"

#define DEBUG_TYPE "verify_mc_invariants"
#undef DEBUG

using namespace llvm;

namespace {
struct MCInvariantVerifier : public InstVisitor<MCInvariantVerifier> {
    bool Broken = false;

private:
    void Check(bool Cond, const char *message, Value *Val) JL_NOTSAFEPOINT {
        if (!Cond) {
            dbgs() << message << "\n\t" << *Val << "\n";
            Broken = true;
        }
    }

public:
    void visitAllocaInst(AllocaInst &AI) JL_NOTSAFEPOINT {
        Check(!isa<ConstantInt>(AI.getArraySize()) ||
                  AI.getParent() == &AI.getFunction()->getEntryBlock(),
              "Constant-size alloca outside the entry block (hidden dynamic alloca)",
              &AI);
    }

    void visitCallBase(CallBase &CB) JL_NOTSAFEPOINT {
        Function *Callee = CB.getCalledFunction();
        if (!Callee)
            return;
        StringRef Name = Callee->getName();
        if (!Name.starts_with("julia."))
            return;
        // Runtime intrinsics the lowering section must have consumed. Marker
        // intrinsics that later stages still understand are not listed.
        bool MustBeLowered = Name == "julia.get_pgcstack" ||
                             Name == "julia.get_pgcstack_or_new" ||
                             Name == "julia.new_gc_frame" ||
                             Name == "julia.push_gc_frame" ||
                             Name == "julia.pop_gc_frame" ||
                             Name == "julia.get_gc_frame_slot" ||
                             Name == "julia.gc_alloc_bytes" ||
                             Name == "julia.gc_alloc_obj" ||
                             Name == "julia.queue_gc_root" ||
                             Name == "julia.safepoint" ||
                             Name == "julia.write_barrier" ||
                             Name == "julia.call" || Name == "julia.call2" ||
                             Name == "julia.call3";
        Check(!MustBeLowered, "Unlowered julia intrinsic after lowering section",
              &CB);
    }
};
}  // anonymous namespace

PreservedAnalyses MCInvariantVerifierPass::run(Function &F, FunctionAnalysisManager &AM)
{
    MCInvariantVerifier V;
    V.visit(F);
    if (V.Broken) {
        abort();
    }
    return PreservedAnalyses::all();
}
