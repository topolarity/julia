; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='function(LateLowerGCFrame)' -S %s | FileCheck %s

; Tests for GC frame slot packing of return_roots / argument-roots buffers and
; for eliding GC frame homes of terminally-rooted buffers.

declare ptr @julia.get_pgcstack()
declare void @julia.gc_roots_begin(ptr captures(none)) #0
declare swiftcc void @callee_sret(ptr noalias noundef captures(none) sret({ ptr addrspace(10), i64 }), ptr noalias noundef captures(none) "julia.return_roots"="1", ptr nonnull swiftself)
declare swiftcc { ptr addrspace(10), i8 } @callee_union(ptr noalias noundef captures(none), ptr noalias noundef captures(none) "julia.return_roots"="1", ptr nonnull swiftself)
declare swiftcc void @use_buf(ptr noundef readonly captures(none), ptr nonnull swiftself)
declare void @use_value(i64)

@const_cell = external constant ptr addrspace(10)

; Two sret+return_roots call sites with disjoint buffer live ranges must share
; one GC frame slot. When an occupant dies, the slot is re-zeroed so the GC
; does not retain the previous occupant's stale roots.
define swiftcc void @pack_disjoint_return_roots() {
; CHECK-LABEL: @pack_disjoint_return_roots
; CHECK: %gcframe = call ptr @julia.new_gc_frame(i32 1)
; CHECK: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 0)
; CHECK-NOT: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 1)
; CHECK: %bits1 = load i64, ptr %bits1p
; CHECK-NEXT: getelementptr inbounds i8, ptr %roots1, i64 0
; CHECK-NEXT: store ptr addrspace(10) null
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %sret1 = alloca { ptr addrspace(10), i64 }, align 8
  %roots1 = alloca ptr addrspace(10), align 8
  %sret2 = alloca { ptr addrspace(10), i64 }, align 8
  %roots2 = alloca ptr addrspace(10), align 8
  call swiftcc void @callee_sret(ptr sret({ ptr addrspace(10), i64 }) %sret1, ptr "julia.return_roots"="1" %roots1, ptr swiftself %pgcstack)
  %bits1p = getelementptr inbounds i8, ptr %sret1, i64 8
  %bits1 = load i64, ptr %bits1p, align 8
  call void @use_value(i64 %bits1)
  call swiftcc void @callee_sret(ptr sret({ ptr addrspace(10), i64 }) %sret2, ptr "julia.return_roots"="1" %roots2, ptr swiftself %pgcstack)
  %bits2p = getelementptr inbounds i8, ptr %sret2, i64 8
  %bits2 = load i64, ptr %bits2p, align 8
  call void @use_value(i64 %bits2)
  ret void
}

; The union-return convention passes the payload buffer at operand 0 without
; an sret attribute; the roots buffer must still pair with it (and stay live
; while the payload is readable through the box-vs-payload select), then share
; a slot with a later disjoint buffer.
define swiftcc void @pack_union_return() {
; CHECK-LABEL: @pack_union_return
; CHECK: %gcframe = call ptr @julia.new_gc_frame(i32 1)
; CHECK: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 0)
; CHECK-NOT: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 1)
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %payload = alloca [2 x i64], align 8
  %uroots = alloca ptr addrspace(10), align 8
  %sret2 = alloca { ptr addrspace(10), i64 }, align 8
  %roots2 = alloca ptr addrspace(10), align 8
  %ret = call swiftcc { ptr addrspace(10), i8 } @callee_union(ptr %payload, ptr "julia.return_roots"="1" %uroots, ptr swiftself %pgcstack)
  %box = extractvalue { ptr addrspace(10), i8 } %ret, 0
  %tag = extractvalue { ptr addrspace(10), i8 } %ret, 1
  %isbox = icmp eq i8 %tag, 1
  %payload11 = addrspacecast ptr %payload to ptr addrspace(11)
  %box11 = addrspacecast ptr addrspace(10) %box to ptr addrspace(11)
  %data = select i1 %isbox, ptr addrspace(11) %box11, ptr addrspace(11) %payload11
  %v = load i64, ptr addrspace(11) %data, align 8
  call void @use_value(i64 %v)
  call swiftcc void @callee_sret(ptr sret({ ptr addrspace(10), i64 }) %sret2, ptr "julia.return_roots"="1" %roots2, ptr swiftself %pgcstack)
  %bits2p = getelementptr inbounds i8, ptr %sret2, i64 8
  %bits2 = load i64, ptr %bits2p, align 8
  call void @use_value(i64 %bits2)
  ret void
}

; Argument-roots staging buffers marked with julia.gc_roots_begin: the marker
; bounds each buffer's live range, so buffers staged for consecutive calls
; share one slot and the marker itself is deleted.
define swiftcc void @pack_argument_roots(ptr addrspace(10) %p) {
; CHECK-LABEL: @pack_argument_roots
; CHECK: %gcframe = call ptr @julia.new_gc_frame(i32 1)
; CHECK: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 0)
; CHECK-NOT: call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 1)
; CHECK-NOT: julia.gc_roots_begin
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %argroots1 = alloca ptr addrspace(10), align 8
  %argroots2 = alloca ptr addrspace(10), align 8
  %x = load ptr addrspace(10), ptr addrspace(10) %p, align 8
  call void @julia.gc_roots_begin(ptr %argroots1)
  store ptr addrspace(10) %x, ptr %argroots1, align 8
  call swiftcc void @use_buf(ptr readonly %argroots1, ptr swiftself %pgcstack)
  %y = load ptr addrspace(10), ptr addrspace(10) %p, align 8
  call void @julia.gc_roots_begin(ptr %argroots2)
  store ptr addrspace(10) %y, ptr %argroots2, align 8
  call swiftcc void @use_buf(ptr readonly %argroots2, ptr swiftself %pgcstack)
  ret void
}

; A buffer whose only stored value is terminally rooted (here: loaded from a
; constant global cell) never needs a GC-visible home: it stays an alloca,
; zero-initialized to preserve the GC frame's null-before-first-store
; semantics. A buffer holding a value the GC may be responsible for keeps a
; GC frame slot.
define swiftcc void @elide_terminally_rooted(ptr addrspace(10) %p) {
; CHECK-LABEL: @elide_terminally_rooted
; CHECK: %gcframe = call ptr @julia.new_gc_frame(i32 1)
; CHECK: %buf_plain = call ptr @julia.get_gc_frame_slot(ptr %gcframe, i32 0)
; CHECK: %buf_refined = alloca ptr addrspace(10)
; CHECK: call void @llvm.memset.p0.i64(ptr align 8 %buf_refined, i8 0, i64 8, i1 false)
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %buf_refined = alloca ptr addrspace(10), align 8
  %buf_plain = alloca ptr addrspace(10), align 8
  %v1 = load ptr addrspace(10), ptr @const_cell, align 8
  store ptr addrspace(10) %v1, ptr %buf_refined, align 8
  call swiftcc void @use_buf(ptr readonly %buf_refined, ptr swiftself %pgcstack)
  %v2 = load ptr addrspace(10), ptr addrspace(10) %p, align 8
  store ptr addrspace(10) %v2, ptr %buf_plain, align 8
  call swiftcc void @use_buf(ptr readonly %buf_plain, ptr swiftself %pgcstack)
  ret void
}

attributes #0 = { nounwind willreturn norecurse nosync memory(argmem: readwrite) }
