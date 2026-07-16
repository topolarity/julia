; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: not --crash opt --load-pass-plugin=libjulia-codegen%shlibext -passes='function(MCInvariantVerifier)' -S %s 2>&1 | FileCheck %s

; Runtime intrinsics must have been consumed by the lowering section; one
; that survives either fails to link or silently loses its semantics.
declare ptr @julia.get_pgcstack()

; CHECK: Unlowered julia intrinsic after lowering section
define ptr @unlowered_intrinsic() {
top:
  %pg = call ptr @julia.get_pgcstack()
  ret ptr %pg
}
