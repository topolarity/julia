# COUNTER-EXAMPLE: branchy call-dense loop the splitter does not help (yet)

A loop whose body is N range-checked diamonds, each arm making a leaf call and
merging via a phi (~4N blocks in one loop body). Reproduces super-linear
compile on the huge loop body.

## Measured (julia pipeline via opt, N=2000)

    off  Total 15.2s  (IndVarSimplify 10.4, InstCombine 2.2, ConstraintElim 2.1)
    F    Total 15.4s  (no help)
    B    Total 15.8s  (no help)

## Why it's a counter-example

Neither block- nor function-splitting bounds this: the splitter forms regions
out of basic blocks and cannot outline a single loop's interior, so the loop
stays whole and the loop-scoped passes (IndVarSimplify, ConstraintElimination)
still process all N diamonds. This is the one shape in our collection where the
current pass provides no lever.

Future work: generalize the splitter to cut/outline loop sub-regions (or hoist
loop-invariant chunks) so this shape gets a lever too.

## Reproduce

    opt -load-pass-plugin=libjulia-codegen.so --passes='julia<llvm_only;no_lower_intrinsics>' \
        -time-passes q.ll -o /dev/null
