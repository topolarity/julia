#include "../cli/trampolines/common.h"

#if defined(__ELF__) && (defined(__x86_64__) || defined(__i386__) || defined(__riscv))
.section .note.GNU-stack,"",@progbits
#elif defined(__ELF__) && (defined(__aarch64__) || defined(__arm__))
.section .note.GNU-stack,"",%progbits
#endif

// Reentry trampoline for lazy ccall PLT stubs.
//
// When a lazy PLT stub is called for the first time, the jump stub loads a
// pointer that points here. This trampoline:
//   1. Saves all ABI argument registers
//   2. Calls ccall_resolve_and_patch(caller_addr) to resolve the ccall
//   3. Restores all registers
//   4. Jumps to the resolved target
//
// After resolution, the stub pointer is patched to point directly at the
// target, so this trampoline is only called once per ccall site.

#if defined(__arm64__) || defined(__aarch64__)

    .text

    .globl CNAME(ccall_reentry_trampoline)
    DEBUGINFO(ccall_reentry_trampoline)
CNAME(ccall_reentry_trampoline):
    .cfi_startproc

    // Per-CCall trampoline reaches us via `b` (no link), having pushed
    // &csymbol_data_t onto the stack (with `str x16, [sp, #-16]!`). lr still
    // holds the user's call-site retaddr. The stack on entry is:
    //   (sp)+0:  &data
    //   (sp)+8:  (alignment padding from the str's 16-byte pre-decrement)
    // and the user's call-site retaddr is in lr.
    //
    // Pushing &data instead of leaving it in x16 makes us robust against
    // the system PLT clobbering x16/x17 on lazy-resolve.
    //
    // We must save lr (since `bl ccall_resolve_and_patch` below will
    // clobber it) along with all argument-passing registers.
    //
    // Frame layout (from sp after stp/sub):
    //   0x00-0x07: x0
    //   0x08-0x0f: x1
    //   0x10-0x17: x2
    //   0x18-0x1f: x3
    //   0x20-0x27: x4
    //   0x28-0x2f: x5
    //   0x30-0x37: x6
    //   0x38-0x3f: x7
    //   0x40-0x4f: q0
    //   0x50-0x5f: q1
    //   0x60-0x6f: q2
    //   0x70-0x7f: q3
    //   0x80-0x8f: q4
    //   0x90-0x9f: q5
    //   0xa0-0xaf: q6
    //   0xb0-0xbf: q7
    //   0xc0-0xc7: x8 (indirect result)
    //   0xc8-0xcf: lr (saved across bl)
    //   Total: 0xd0 (208 bytes). 16-byte aligned.

    stp     x0, x1, [sp, #-0xd0]!
    .cfi_def_cfa_offset 0xd0
    .cfi_rel_offset x0, 0x00
    .cfi_rel_offset x1, 0x08
    stp     x2, x3, [sp, #0x10]
    .cfi_rel_offset x2, 0x10
    .cfi_rel_offset x3, 0x18
    stp     x4, x5, [sp, #0x20]
    .cfi_rel_offset x4, 0x20
    .cfi_rel_offset x5, 0x28
    stp     x6, x7, [sp, #0x30]
    .cfi_rel_offset x6, 0x30
    .cfi_rel_offset x7, 0x38
    stp     q0, q1, [sp, #0x40]
    .cfi_rel_offset q0, 0x40
    .cfi_rel_offset q1, 0x50
    stp     q2, q3, [sp, #0x60]
    .cfi_rel_offset q2, 0x60
    .cfi_rel_offset q3, 0x70
    stp     q4, q5, [sp, #0x80]
    .cfi_rel_offset q4, 0x80
    .cfi_rel_offset q5, 0x90
    stp     q6, q7, [sp, #0xa0]
    .cfi_rel_offset q6, 0xa0
    .cfi_rel_offset q7, 0xb0
    str     x8,  [sp, #0xc0]
    .cfi_rel_offset x8, 0xc0
    str     lr,  [sp, #0xc8]
    .cfi_rel_offset lr, 0xc8

    // Load &data from the trampoline-pushed slot (above our frame, at
    // offset 0xd0) into x0 (AAPCS first-arg) for the C resolver.
    ldr     x0, [sp, #0xd0]

    bl      CNAME(ccall_resolve_and_patch)
    mov     x16, x0    // save resolved target across reg restores

    // Restore all saved registers.
    ldr     lr,  [sp, #0xc8]
    .cfi_restore lr
    ldr     x8,  [sp, #0xc0]
    .cfi_restore x8
    ldp     q6, q7, [sp, #0xa0]
    .cfi_restore q6
    .cfi_restore q7
    ldp     q4, q5, [sp, #0x80]
    .cfi_restore q4
    .cfi_restore q5
    ldp     q2, q3, [sp, #0x60]
    .cfi_restore q2
    .cfi_restore q3
    ldp     q0, q1, [sp, #0x40]
    .cfi_restore q0
    .cfi_restore q1
    ldp     x6, x7, [sp, #0x30]
    .cfi_restore x6
    .cfi_restore x7
    ldp     x4, x5, [sp, #0x20]
    .cfi_restore x4
    .cfi_restore x5
    ldp     x2, x3, [sp, #0x10]
    .cfi_restore x2
    .cfi_restore x3
    // Restore x0/x1, drop our frame (0xd0), and drop the trampoline-pushed
    // &data (16) all together. (ldp's post-index handles 0xd0; we add the
    // remaining 16 explicitly.) lr still holds the user's call-site retaddr,
    // so the resolved target's `ret` returns directly to the user.
    ldp     x0, x1, [sp], #0xd0
    .cfi_restore x0
    .cfi_restore x1
    add     sp, sp, #16
    .cfi_def_cfa_offset 0

    br      x16
    .cfi_endproc
    EXPORT(ccall_reentry_trampoline)

#endif // defined(__arm64__) || defined(__aarch64__)

#if defined(__x86_64__) && !defined(_WIN64)

    .text

    .globl CNAME(ccall_reentry_trampoline)
    DEBUGINFO(ccall_reentry_trampoline)
CNAME(ccall_reentry_trampoline):
    .cfi_startproc
    CET_START()

    // Reached by tail-jump from the per-CCall trampoline, which has already
    // pushed an 8-byte alignment pad and &csymbol_data_t on the stack. The
    // stack on entry is:
    //   (%rsp)+0:  &data         (pushed by trampoline, 2nd push)
    //   (%rsp)+8:  0             (pushed by trampoline, 1st push — pad)
    //   (%rsp)+16: retaddr_user  (pushed by user's `call <stub>`)
    //
    // Pushing &data instead of leaving it in %r11 makes us robust against
    // the system PLT clobbering scratch registers on lazy-resolve. Pushing
    // a 2nd (pad) slot makes the trampoline push 16 bytes total, so this
    // resolver is entered with %rsp = 8 mod 16 — the standard SysV "after
    // `call`" alignment that _dl_runtime_resolve assumes when binding
    // ccall_reentry_trampoline itself on the first call.
    //
    // Save all SysV ABI argument-passing registers; %r10/%r11 are scratch
    // and don't carry user state worth saving.
    //
    // Frame layout (from rsp after sub):
    //   0x00-0x07: rdi
    //   0x08-0x0f: rsi
    //   0x10-0x17: rdx
    //   0x18-0x1f: rcx
    //   0x20-0x27: r8
    //   0x28-0x2f: r9
    //   0x30-0x37: rax
    //   0x38-0x3f: (padding)
    //   0x40-0x4f: xmm0
    //   0x50-0x5f: xmm1
    //   0x60-0x6f: xmm2
    //   0x70-0x7f: xmm3
    //   0x80-0x8f: xmm4
    //   0x90-0x9f: xmm5
    //   0xa0-0xaf: xmm6
    //   0xb0-0xbf: xmm7
    //   0xc0-0xc7: (padding — keeps 16-byte alignment given entry rsp=8 mod 16)
    //   0xc8:      &data         (above the frame, pushed by trampoline)
    //   0xd0:      0             (above the frame, pushed by trampoline as pad)
    //   0xd8:      retaddr_user
    //   Total frame: 0xc8 (200 bytes)
    //
    // On entry rsp is 8-mod-16 (user push 8, trampoline push 16 = 24, so
    // (8 + 8 + 16) mod 16 = 8). After subq $0xc8: rsp is 0 mod 16. Aligned
    // for callq below.

    subq    $0xc8, %rsp
    .cfi_def_cfa_offset 0xc8 + 16   // +16 for trampoline-pushed (&data + pad)

    movq    %rdi, 0x00(%rsp)
    .cfi_rel_offset rdi, 0x00
    movq    %rsi, 0x08(%rsp)
    .cfi_rel_offset rsi, 0x08
    movq    %rdx, 0x10(%rsp)
    .cfi_rel_offset rdx, 0x10
    movq    %rcx, 0x18(%rsp)
    .cfi_rel_offset rcx, 0x18
    movq    %r8,  0x20(%rsp)
    .cfi_rel_offset r8, 0x20
    movq    %r9,  0x28(%rsp)
    .cfi_rel_offset r9, 0x28
    movq    %rax, 0x30(%rsp)
    .cfi_rel_offset rax, 0x30

    movdqu  %xmm0, 0x40(%rsp)
    .cfi_rel_offset xmm0, 0x40
    movdqu  %xmm1, 0x50(%rsp)
    .cfi_rel_offset xmm1, 0x50
    movdqu  %xmm2, 0x60(%rsp)
    .cfi_rel_offset xmm2, 0x60
    movdqu  %xmm3, 0x70(%rsp)
    .cfi_rel_offset xmm3, 0x70
    movdqu  %xmm4, 0x80(%rsp)
    .cfi_rel_offset xmm4, 0x80
    movdqu  %xmm5, 0x90(%rsp)
    .cfi_rel_offset xmm5, 0x90
    movdqu  %xmm6, 0xa0(%rsp)
    .cfi_rel_offset xmm6, 0xa0
    movdqu  %xmm7, 0xb0(%rsp)
    .cfi_rel_offset xmm7, 0xb0

    // Load &data from the trampoline-pushed slot (above our frame) into
    // %rdi (SysV first-arg) for the C resolver.
    movq    0xc8(%rsp), %rdi

    callq   CNAME(ccall_resolve_and_patch)
    movq    %rax, %r11   // save resolved target across reg restores

    // Restore all registers
    movdqu  0xb0(%rsp), %xmm7
    .cfi_restore xmm7
    movdqu  0xa0(%rsp), %xmm6
    .cfi_restore xmm6
    movdqu  0x90(%rsp), %xmm5
    .cfi_restore xmm5
    movdqu  0x80(%rsp), %xmm4
    .cfi_restore xmm4
    movdqu  0x70(%rsp), %xmm3
    .cfi_restore xmm3
    movdqu  0x60(%rsp), %xmm2
    .cfi_restore xmm2
    movdqu  0x50(%rsp), %xmm1
    .cfi_restore xmm1
    movdqu  0x40(%rsp), %xmm0
    .cfi_restore xmm0

    movq    0x30(%rsp), %rax
    .cfi_restore rax
    movq    0x28(%rsp), %r9
    .cfi_restore r9
    movq    0x20(%rsp), %r8
    .cfi_restore r8
    movq    0x18(%rsp), %rcx
    .cfi_restore rcx
    movq    0x10(%rsp), %rdx
    .cfi_restore rdx
    movq    0x08(%rsp), %rsi
    .cfi_restore rsi
    movq    0x00(%rsp), %rdi
    .cfi_restore rdi

    // Drop our frame (0xc8) AND the trampoline-pushed slots (16: &data + pad)
    // in one shot. After this, (%rsp) holds the user's call-site retaddr;
    // jumping to the resolved target via %r11 means the target's `ret`
    // returns directly to the user's code.
    addq    $0xd8, %rsp
    .cfi_def_cfa_offset 8

    jmpq    *%r11
    .cfi_endproc
    EXPORT(ccall_reentry_trampoline)

#endif // defined(__x86_64__) && !defined(_WIN64)

#if defined(_WIN64)

    .text

    .globl CNAME(ccall_reentry_trampoline)
    DEBUGINFO(ccall_reentry_trampoline)
CNAME(ccall_reentry_trampoline):
    SEH_START1(ccall_reentry_trampoline)
    .cfi_startproc
    CET_START()

    // On entry, the original caller did `call <stub>`, which pushed a return
    // address onto the stack. The stub is a JITLink indirect jump:
    //   jmpq *(%rip)    ; 6 bytes — FF 25 00 00 00 00
    // This is a tail-jump, so the stack still has just the original caller's
    // return address at (%rsp). No red zone on Windows.

    // Save all Microsoft x64 ABI argument registers:
    //   Integer: rcx, rdx, r8, r9 (4 regs)
    //   SSE: xmm0-xmm3 (4 x 16 bytes = 64 bytes)
    //
    // Frame layout (from rsp after sub):
    //   0x00-0x1f: shadow space for callq (32 bytes)
    //   0x20-0x27: rcx
    //   0x28-0x2f: rdx
    //   0x30-0x37: r8
    //   0x38-0x3f: r9
    //   0x40-0x4f: xmm0
    //   0x50-0x5f: xmm1
    //   0x60-0x6f: xmm2
    //   0x70-0x7f: xmm3
    //   0x80-0x87: (alignment padding)
    //   Total: 0x88 (136 bytes)
    //
    // On entry rsp is 8-mod-16 (return address pushed by caller).
    // After subq $0x88: rsp is (8+0x88)=0x90 below original = 0 mod 16.
    // This ensures 16-byte alignment for the callq below.

    subq    $0x88, %rsp
    .seh_stackalloc 0x88
    .cfi_def_cfa_offset 0x88 + 8    // +8 for return address
    SEH_START2()

    movq    %rcx, 0x20(%rsp)
    .cfi_rel_offset rcx, 0x20
    movq    %rdx, 0x28(%rsp)
    .cfi_rel_offset rdx, 0x28
    movq    %r8,  0x30(%rsp)
    .cfi_rel_offset r8, 0x30
    movq    %r9,  0x38(%rsp)
    .cfi_rel_offset r9, 0x38

    movdqu  %xmm0, 0x40(%rsp)
    .cfi_rel_offset xmm0, 0x40
    movdqu  %xmm1, 0x50(%rsp)
    .cfi_rel_offset xmm1, 0x50
    movdqu  %xmm2, 0x60(%rsp)
    .cfi_rel_offset xmm2, 0x60
    movdqu  %xmm3, 0x70(%rsp)
    .cfi_rel_offset xmm3, 0x70

    // Compute stub entry address to pass to the resolver.
    // Return address is at 0x88(%rsp), past our frame.
    movq    0x88(%rsp), %rcx

    callq   CNAME(ccall_resolve_and_patch)
    movq    %rax, %r11

    // Restore all registers
    movdqu  0x70(%rsp), %xmm3
    .cfi_restore xmm3
    movdqu  0x60(%rsp), %xmm2
    .cfi_restore xmm2
    movdqu  0x50(%rsp), %xmm1
    .cfi_restore xmm1
    movdqu  0x40(%rsp), %xmm0
    .cfi_restore xmm0

    movq    0x38(%rsp), %r9
    .cfi_restore r9
    movq    0x30(%rsp), %r8
    .cfi_restore r8
    movq    0x28(%rsp), %rdx
    .cfi_restore rdx
    movq    0x20(%rsp), %rcx
    .cfi_restore rcx

    addq    $0x88, %rsp
    .cfi_def_cfa_offset 8

    // The original caller's return address is at (%rsp). Jump to the resolved
    // target — it will return directly to the original caller.
    jmpq    *%r11
    SEH_END()
    .cfi_endproc
    EXPORT(ccall_reentry_trampoline)

#endif // defined(_WIN64)

#if defined(__i386__) || defined(_M_IX86)

    .text

    .globl CNAME(ccall_reentry_trampoline)
    DEBUGINFO(ccall_reentry_trampoline)
CNAME(ccall_reentry_trampoline):
    .cfi_startproc
    CET_START()

    // i686 cdecl: all arguments are passed on the stack, so we don't need to
    // save any argument registers. We only need to preserve the return address
    // for the resolver and make sure the stack stays aligned.
    //
    // On entry, the original caller did `call <stub>`, which pushed a return
    // address. The stub does `jmpl *(<addr>)` which is transparent.
    // Stack: [esp] = return address. ESP is 4-byte aligned (after push of retaddr).
    //
    // Frame layout (from esp after sub):
    //   0x00-0x03: arg0 for ccall_resolve_and_patch (caller_addr)
    //   0x04-0x0f: (padding for 16-byte alignment)
    //   Total: 0x10 (16 bytes)
    //
    // cdecl requires 16-byte alignment before `call`. On entry esp is
    // (aligned - 4) due to the return address push. After sub $0x0c:
    // esp is (aligned - 4 - 0x0c) = (aligned - 0x10) = aligned. Good.

    subl    $0x0c, %esp
    .cfi_def_cfa_offset 0x0c + 4    // +4 for return address

    // Pass the return address as the first argument
    movl    0x0c(%esp), %eax
    movl    %eax, 0x00(%esp)

    calll   CNAME(ccall_resolve_and_patch)

    addl    $0x0c, %esp
    .cfi_def_cfa_offset 4

    // eax = resolved address. Jump to it with the original caller's return
    // address and stack arguments still in place.
    jmpl    *%eax
    .cfi_endproc

#endif // defined(__i386__) || defined(_M_IX86)

#if defined(__arm__) && !defined(__aarch64__)

    .text
    .syntax unified
    .thumb

    .globl CNAME(ccall_reentry_trampoline)
    .thumb_func
CNAME(ccall_reentry_trampoline):
    .cfi_startproc

    // ARM EABI (hard-float), Thumb-2: arguments in r0-r3 and d0-d7.
    // On entry, the original caller did `bl <stub>`, which set lr = return
    // address. The stub does `ldr pc, [<addr>]` which is transparent to lr.
    //
    // Frame layout (from sp after sub):
    //   0x00-0x03: r0
    //   0x04-0x07: r1
    //   0x08-0x0b: r2
    //   0x0c-0x0f: r3
    //   0x10-0x13: lr (return address)
    //   0x14-0x17: (padding for 8-byte alignment)
    //   0x18-0x57: d0-d7 (8 x 8 bytes = 64 bytes)
    //   Total: 0x58 (88 bytes)
    //
    // ARM AAPCS requires 8-byte stack alignment at public interfaces.
    // On entry sp is 8-byte aligned (guaranteed by AAPCS).
    // After sub: sp -= 0x58 = 88, which is 0 mod 8. Still aligned.

    sub     sp, sp, #0x58
    .cfi_def_cfa_offset 0x58

    str     r0, [sp, #0x00]
    .cfi_rel_offset r0, 0x00
    str     r1, [sp, #0x04]
    .cfi_rel_offset r1, 0x04
    str     r2, [sp, #0x08]
    .cfi_rel_offset r2, 0x08
    str     r3, [sp, #0x0c]
    .cfi_rel_offset r3, 0x0c
    str     lr, [sp, #0x10]
    .cfi_rel_offset lr, 0x10

#if !defined(__SOFTFP__)
    add     ip, sp, #0x18
    vstm    ip, {d0-d7}
    .cfi_rel_offset d0, 0x18
    .cfi_rel_offset d1, 0x20
    .cfi_rel_offset d2, 0x28
    .cfi_rel_offset d3, 0x30
    .cfi_rel_offset d4, 0x38
    .cfi_rel_offset d5, 0x40
    .cfi_rel_offset d6, 0x48
    .cfi_rel_offset d7, 0x50
#endif

    // Pass the return address as the first argument
    mov     r0, lr

    bl      CNAME(ccall_resolve_and_patch)
    mov     ip, r0

    // Restore all registers
#if !defined(__SOFTFP__)
    add     r0, sp, #0x18
    vldm    r0, {d0-d7}
    .cfi_restore d0
    .cfi_restore d1
    .cfi_restore d2
    .cfi_restore d3
    .cfi_restore d4
    .cfi_restore d5
    .cfi_restore d6
    .cfi_restore d7
#endif

    ldr     lr, [sp, #0x10]
    .cfi_restore lr
    ldr     r3, [sp, #0x0c]
    .cfi_restore r3
    ldr     r2, [sp, #0x08]
    .cfi_restore r2
    ldr     r1, [sp, #0x04]
    .cfi_restore r1
    ldr     r0, [sp, #0x00]
    .cfi_restore r0

    add     sp, sp, #0x58
    .cfi_def_cfa_offset 0

    bx      ip
    .cfi_endproc

#endif // defined(__arm__) && !defined(__aarch64__)

#if defined(__riscv) && __riscv_xlen == 64

    .text

    .globl CNAME(ccall_reentry_trampoline)
    DEBUGINFO(ccall_reentry_trampoline)
CNAME(ccall_reentry_trampoline):
    .cfi_startproc

    // RISC-V LP64D: integer args in a0-a7, float args in fa0-fa7.
    // On entry, the original caller did `call <stub>` (auipc+jalr), which set
    // ra = return address. The stub does `jr t0` which is transparent to ra.
    //
    // The per-CCall trampoline reaches us via `tail` (jalr zero, ...),
    // having pushed &csymbol_data_t and 8 bytes of alignment pad onto the
    // stack with `addi sp, sp, -16; sd t0, 0(sp)`. The stack on entry is:
    //   (sp)+0x00:  &data         (pushed by trampoline)
    //   (sp)+0x08:  (pad — undefined contents)
    //   (sp)+0x10:  (caller's stack as it was before the call to <stub>)
    // and ra holds the user's call-site retaddr.
    //
    // Pushing &data instead of leaving it in t0 makes us robust against the
    // system PLT clobbering scratch registers on lazy-resolve.
    //
    // Frame layout (from sp after addi):
    //   0x00-0x07: a0 (x10)
    //   0x08-0x0f: a1 (x11)
    //   0x10-0x17: a2 (x12)
    //   0x18-0x1f: a3 (x13)
    //   0x20-0x27: a4 (x14)
    //   0x28-0x2f: a5 (x15)
    //   0x30-0x37: a6 (x16)
    //   0x38-0x3f: a7 (x17)
    //   0x40-0x47: ra (saved across `call`)
    //   0x48-0x4f: (padding — keeps frame size 16-byte aligned)
    //   0x50-0x57: fa0 (f10)
    //   0x58-0x5f: fa1 (f11)
    //   0x60-0x67: fa2 (f12)
    //   0x68-0x6f: fa3 (f13)
    //   0x70-0x77: fa4 (f14)
    //   0x78-0x7f: fa5 (f15)
    //   0x80-0x87: fa6 (f16)
    //   0x88-0x8f: fa7 (f17)
    //   0x90:      &data (above the frame, pushed by trampoline)
    //   0x98:      (pad, pushed by trampoline)
    //   Total frame: 0x90 (144 bytes)
    //
    // RISC-V psABI requires 16-byte stack alignment at function entry.
    // The trampoline pushed 16 bytes, so sp is still 16-byte aligned on
    // entry. After addi: sp -= 0x90, which preserves alignment.

    addi    sp, sp, -0x90
    .cfi_def_cfa_offset 0x90 + 16   // +16 for trampoline-pushed (&data + pad)

    sd      a0, 0x00(sp)
    .cfi_rel_offset x10, 0x00
    sd      a1, 0x08(sp)
    .cfi_rel_offset x11, 0x08
    sd      a2, 0x10(sp)
    .cfi_rel_offset x12, 0x10
    sd      a3, 0x18(sp)
    .cfi_rel_offset x13, 0x18
    sd      a4, 0x20(sp)
    .cfi_rel_offset x14, 0x20
    sd      a5, 0x28(sp)
    .cfi_rel_offset x15, 0x28
    sd      a6, 0x30(sp)
    .cfi_rel_offset x16, 0x30
    sd      a7, 0x38(sp)
    .cfi_rel_offset x17, 0x38
    sd      ra, 0x40(sp)
    .cfi_rel_offset x1, 0x40

    fsd     fa0, 0x50(sp)
    .cfi_rel_offset f10, 0x50
    fsd     fa1, 0x58(sp)
    .cfi_rel_offset f11, 0x58
    fsd     fa2, 0x60(sp)
    .cfi_rel_offset f12, 0x60
    fsd     fa3, 0x68(sp)
    .cfi_rel_offset f13, 0x68
    fsd     fa4, 0x70(sp)
    .cfi_rel_offset f14, 0x70
    fsd     fa5, 0x78(sp)
    .cfi_rel_offset f15, 0x78
    fsd     fa6, 0x80(sp)
    .cfi_rel_offset f16, 0x80
    fsd     fa7, 0x88(sp)
    .cfi_rel_offset f17, 0x88

    // Load &data from the trampoline-pushed slot (above our frame, at
    // offset 0x90) into a0 (LP64D first-arg) for the C resolver.
    ld      a0, 0x90(sp)

    call    CNAME(ccall_resolve_and_patch)
    mv      t0, a0    // save resolved target across reg restores

    // Restore all registers
    fld     fa7, 0x88(sp)
    .cfi_restore f17
    fld     fa6, 0x80(sp)
    .cfi_restore f16
    fld     fa5, 0x78(sp)
    .cfi_restore f15
    fld     fa4, 0x70(sp)
    .cfi_restore f14
    fld     fa3, 0x68(sp)
    .cfi_restore f13
    fld     fa2, 0x60(sp)
    .cfi_restore f12
    fld     fa1, 0x58(sp)
    .cfi_restore f11
    fld     fa0, 0x50(sp)
    .cfi_restore f10

    ld      ra, 0x40(sp)
    .cfi_restore x1
    ld      a7, 0x38(sp)
    .cfi_restore x17
    ld      a6, 0x30(sp)
    .cfi_restore x16
    ld      a5, 0x28(sp)
    .cfi_restore x15
    ld      a4, 0x20(sp)
    .cfi_restore x14
    ld      a3, 0x18(sp)
    .cfi_restore x13
    ld      a2, 0x10(sp)
    .cfi_restore x12
    ld      a1, 0x08(sp)
    .cfi_restore x11
    ld      a0, 0x00(sp)
    .cfi_restore x10

    // Drop our frame (0x90) AND the trampoline-pushed slots (16: &data + pad)
    // in one shot. ra holds the user's call-site retaddr; jumping to the
    // resolved target via t0 means the target's `ret` returns directly to
    // the user's code.
    addi    sp, sp, 0xa0
    .cfi_def_cfa_offset 0

    jr      t0
    .cfi_endproc
    EXPORT(ccall_reentry_trampoline)

#endif // defined(__riscv) && __riscv_xlen == 64
