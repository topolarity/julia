; This file is a part of Julia. License is MIT: https://julialang.org/license

; RUN: opt --load-pass-plugin=libjulia-codegen%shlibext -passes='function(PreciseLifetimeEnds)' -S %s | FileCheck %s

declare ptr @julia.get_pgcstack()
declare swiftcc void @callee_sret(ptr noalias noundef captures(none) sret([2 x i64]), ptr nonnull swiftself)
declare swiftcc void @throw_it(ptr noundef readonly captures(none), ptr nonnull swiftself) #0
declare swiftcc void @use_buf(ptr noundef readonly captures(none), ptr nonnull swiftself)
declare void @use_value(i64)
declare void @capture_buf(ptr)

; Sequential sret results whose reads are complete before the next call:
; each buffer's lifetime ends right after its last read, so StackColoring can
; merge their slots even in straight-line code.
define swiftcc void @straight_line() {
; CHECK-LABEL: @straight_line
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r1 = alloca [2 x i64], align 8
  %r2 = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r1)
  call swiftcc void @callee_sret(ptr sret([2 x i64]) %r1, ptr swiftself %pgcstack)
  %v1 = load i64, ptr %r1, align 8
; CHECK: %v1 = load i64, ptr %r1
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %r1)
  call void @use_value(i64 %v1)
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r2)
  call swiftcc void @callee_sret(ptr sret([2 x i64]) %r2, ptr swiftself %pgcstack)
  %v2 = load i64, ptr %r2, align 8
; CHECK: %v2 = load i64, ptr %r2
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %r2)
  call void @use_value(i64 %v2)
  ret void
}

; A buffer staged and consumed inside a loop body: the end goes after the
; last read in the body. Reaching the next iteration's uses passes the
; in-loop lifetime.start, so the single-region admission rule holds.
define swiftcc void @in_loop(i64 %n) {
; CHECK-LABEL: @in_loop
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r = alloca [2 x i64], align 8
  br label %loop

loop:
  %i = phi i64 [ 0, %top ], [ %i2, %loop ]
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r)
  call swiftcc void @callee_sret(ptr sret([2 x i64]) %r, ptr swiftself %pgcstack)
  %v = load i64, ptr %r, align 8
; CHECK: %v = load i64, ptr %r
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %r)
  call void @use_value(i64 %v)
  %i2 = add i64 %i, 1
  %done = icmp sge i64 %i2, %n
  br i1 %done, label %exit, label %loop

exit:
  ret void
}

; The cold-path shape: stores on the hot path, single read in a no-return
; block. The buffer dies on the non-throwing sibling edge.
define swiftcc void @cold_read(i64 %n, i64 %m, i1 %ok) {
; CHECK-LABEL: @cold_read
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %range = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %range)
  store i64 1, ptr %range, align 8
  %hi = getelementptr inbounds i8, ptr %range, i64 8
  store i64 %n, ptr %hi, align 8
  br i1 %ok, label %hot, label %cold
; CHECK: hot:
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %range)

hot:
  call void @use_value(i64 %m)
  ret void

cold:
  call swiftcc void @throw_it(ptr readonly %range, ptr swiftself %pgcstack)
; No end after the throw: an unreachable-terminated block bounds nothing, and
; a second end would cost the slot its first-use anchoring.
; CHECK: call swiftcc void @throw_it
; CHECK-NOT: call void @llvm.lifetime.end
  unreachable
}

; Reads on both paths: the surviving path's last read gets an end; the
; no-return path needs none.
define swiftcc void @both_paths_read(i64 %n, i1 %ok) {
; CHECK-LABEL: @both_paths_read
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %range = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %range)
  store i64 1, ptr %range, align 8
  br i1 %ok, label %hot, label %cold

hot:
  call swiftcc void @use_buf(ptr readonly %range, ptr swiftself %pgcstack)
; CHECK: call swiftcc void @use_buf
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %range)
  ret void

cold:
  call swiftcc void @throw_it(ptr readonly %range, ptr swiftself %pgcstack)
; CHECK: call swiftcc void @throw_it
; CHECK-NOT: call void @llvm.lifetime.end
  unreachable
}

; A (dead) store positioned after the last read violates the admission rule:
; in marker-driven conservative mode it would sit outside the marker region
; and could clobber a merged neighbor. No ends may be inserted.
define swiftcc void @trailing_dead_store(i64 %n) {
; CHECK-LABEL: @trailing_dead_store
; CHECK-NOT: call void @llvm.lifetime.end
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r)
  store i64 %n, ptr %r, align 8
  call swiftcc void @use_buf(ptr readonly %r, ptr swiftself %pgcstack)
  store i64 0, ptr %r, align 8
  ret void
}

; Region re-entry: a full clobber restarts liveness after a dead gap. The
; second region has no start marker of its own, so no ends may be inserted.
define swiftcc void @region_reentry(i64 %n) {
; CHECK-LABEL: @region_reentry
; CHECK-NOT: call void @llvm.lifetime.end
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r = alloca i64, align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r)
  store i64 %n, ptr %r, align 8
  call swiftcc void @use_buf(ptr readonly %r, ptr swiftself %pgcstack)
  call void @use_value(i64 %n)
  store i64 7, ptr %r, align 8
  call swiftcc void @use_buf(ptr readonly %r, ptr swiftself %pgcstack)
  ret void
}

; Escaping buffers are not candidates.
define swiftcc void @escapes(i64 %n) {
; CHECK-LABEL: @escapes
; CHECK-NOT: call void @llvm.lifetime.end
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %r)
  store i64 %n, ptr %r, align 8
  call void @capture_buf(ptr %r)
  ret void
}

attributes #0 = { noreturn }

; A buffer pair read through a pointer phi (the shape SimplifyCFG sinking
; produces): edge-substituting forwarder liveness bounds both buffers at the
; join read.
define swiftcc void @phi_forwarder(i1 %c, i64 %x) {
; CHECK-LABEL: @phi_forwarder
top:
  %A = alloca [2 x i64], align 8
  %B = alloca [2 x i64], align 8
  br i1 %c, label %fa, label %fb

fa:
  call void @llvm.lifetime.start.p0(i64 -1, ptr %A)
  store i64 %x, ptr %A, align 8
  br label %join

fb:
  call void @llvm.lifetime.start.p0(i64 -1, ptr %B)
  store i64 %x, ptr %B, align 8
  br label %join

join:
  %p = phi ptr [ %A, %fa ], [ %B, %fb ]
  %v = load i64, ptr %p, align 8
; CHECK: %v = load i64, ptr %p
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %{{[AB]}})
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %{{[AB]}})
  call void @use_value(i64 %v)
  ret void
}

; The select flavor (if-converted): a read through the select is a may-read
; of both inputs; both die after it.
define swiftcc void @select_forwarder(i1 %c, i64 %x) {
; CHECK-LABEL: @select_forwarder
top:
  %A = alloca [2 x i64], align 8
  %B = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %A)
  store i64 %x, ptr %A, align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %B)
  store i64 %x, ptr %B, align 8
  %p = select i1 %c, ptr %A, ptr %B
  %v = load i64, ptr %p, align 8
; CHECK: %v = load i64, ptr %p
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %{{[AB]}})
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %{{[AB]}})
  call void @use_value(i64 %v)
  ret void
}

; A forwarder whose pointer escapes poisons every buffer it may carry.
define swiftcc void @poisoned_forwarder(i1 %c, i64 %x) {
; CHECK-LABEL: @poisoned_forwarder
; CHECK-NOT: call void @llvm.lifetime.end
top:
  %A = alloca [2 x i64], align 8
  %B = alloca [2 x i64], align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %A)
  store i64 %x, ptr %A, align 8
  call void @llvm.lifetime.start.p0(i64 -1, ptr %B)
  store i64 %x, ptr %B, align 8
  %p = select i1 %c, ptr %A, ptr %B
  call void @capture_buf(ptr %p)
  ret void
}

; A buffer with no markers at all (e.g. after MemCpyOpt's stack-move merges
; two buffers and deletes both allocas' markers) gets a synthesized start at
; its earliest access and precise ends.
define swiftcc void @markerless(i64 %n) {
; CHECK-LABEL: @markerless
top:
  %pgcstack = call ptr @julia.get_pgcstack()
  %r = alloca [2 x i64], align 8
; CHECK: call void @llvm.lifetime.start.p0(i64 -1, ptr %r)
; CHECK-NEXT: store i64 %n, ptr %r
  store i64 %n, ptr %r, align 8
  call swiftcc void @use_buf(ptr readonly %r, ptr swiftself %pgcstack)
; CHECK: call swiftcc void @use_buf
; CHECK-NEXT: call void @llvm.lifetime.end.p0(i64 -1, ptr %r)
  ret void
}
