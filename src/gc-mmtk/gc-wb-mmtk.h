// This file is a part of Julia. License is MIT: https://julialang.org/license

// ========================================================================= //
// Runtime Write-Barriers
// ========================================================================= //

#ifndef JL_GC_WB_H
#define JL_GC_WB_H

#ifdef __cplusplus
extern "C" {
#endif

extern void mmtk_object_reference_write_pre(void* mutator, const void* parent, const void* ptr);
extern void mmtk_object_reference_write_slow(void* mutator, const void* parent, const void* ptr);
extern void* MMTK_SIDE_LOG_BIT_BASE_ADDRESS;
// Marking-gated SATB barrier: nonzero exactly while concurrent marking is
// active.  Checked before the per-object unlog bit so that (a) the barrier
// costs one predictable branch outside marking and (b) unlog bits are never
// consumed outside marking, which lets all arming happen off-pause.
extern uint8_t MMTK_SATB_MARKING_ACTIVE;
extern void mmtk_gc_wb_slots_pre(void* mutator, void** slots, size_t n);
JL_DLLEXPORT void jl_gc_queue_root_slot(const struct _jl_value_t *parent, void **slot);

#define MMTK_OBJECT_BARRIER (1)
// Stickyimmix needs write barrier. Immix does not need write barrier.
#ifdef MMTK_PLAN_IMMIX
#define MMTK_NEEDS_WRITE_BARRIER (0)
#endif
#ifdef MMTK_PLAN_STICKYIMMIX
#define MMTK_NEEDS_WRITE_BARRIER (1)
#endif
// ConcurrentImmix uses a SATB barrier. Since every write barrier is now emitted
// before the store, the same inlined log-bit check works: when the parent's log
// bit is set, the slow path can snapshot its still-current fields.
#ifdef MMTK_PLAN_CONCURRENTIMMIX
#define MMTK_NEEDS_WRITE_BARRIER (1)
#endif

// Directly call into MMTk for write barrier (debugging only). The pre entry is
// emitted before the store, which is correct for both StickyImmix and
// ConcurrentImmix.
STATIC_INLINE void mmtk_gc_wb_full(const void *parent, const void *ptr) JL_NOTSAFEPOINT
{
    jl_task_t *ct = jl_current_task;
    jl_ptls_t ptls = ct->ptls;
    mmtk_object_reference_write_pre(&ptls->gc_tls.mmtk_mutator, parent, ptr);
}

// Inlined fastpath
STATIC_INLINE void mmtk_gc_wb_fast(const void *parent, const void *ptr) JL_NOTSAFEPOINT
{
    if (MMTK_NEEDS_WRITE_BARRIER == MMTK_OBJECT_BARRIER) {
        // ALWAYS-ON BARRIER (ConcurrentImmix): the unlog bit alone gates the
        // slow path.  Armed = old object not yet logged this window; the slow
        // path snapshots fields during marking (SATB) and records the object
        // in the remembered set otherwise.  Young objects are born unarmed,
        // so the common case is one predictable branch.
        intptr_t addr = (intptr_t) (void*) parent;
        uint8_t* meta_addr = (uint8_t*) (MMTK_SIDE_LOG_BIT_BASE_ADDRESS) + (addr >> 6);
        intptr_t shift = (addr >> 3) & 0b111;
        uint8_t byte_val = *meta_addr;
        if (((byte_val >> shift) & 1) == 1) {
            jl_task_t *ct = jl_current_task;
            jl_ptls_t ptls = ct->ptls;
            mmtk_object_reference_write_slow(&ptls->gc_tls.mmtk_mutator, parent, ptr);
        }
    }
}

STATIC_INLINE void jl_gc_wb(const void *parent, const void *ptr) JL_NOTSAFEPOINT
{
    mmtk_gc_wb_fast(parent, ptr);
}

// SLOT-PRECISE pre-store barrier for C store sites: call BEFORE writing
// `*slot`.  Same armed check as `jl_gc_wb`, but the slow path receives the
// store address, so during concurrent marking a large object captures only
// this slot's old value instead of a whole-object field snapshot on the
// mutator (measured: 4-12ms per capture on the 1MB Tuple typename-cache
// svec).  Outside marking, and for small objects, behavior matches
// `jl_gc_wb` (remset + log).  `newval` is unused here; the stock variant
// consumes it.
STATIC_INLINE void jl_gc_wb_slot_pre(const void *parent, void **slot, const void *newval) JL_NOTSAFEPOINT
{
    (void)newval;
    if (MMTK_NEEDS_WRITE_BARRIER == MMTK_OBJECT_BARRIER) {
        intptr_t addr = (intptr_t) (void*) parent;
        uint8_t* meta_addr = (uint8_t*) (MMTK_SIDE_LOG_BIT_BASE_ADDRESS) + (addr >> 6);
        intptr_t shift = (addr >> 3) & 0b111;
        uint8_t byte_val = *meta_addr;
        if (((byte_val >> shift) & 1) == 1) {
            jl_gc_queue_root_slot((const struct _jl_value_t*)parent, slot);
        }
    }
}

STATIC_INLINE void jl_gc_wb_back(const void *ptr) JL_NOTSAFEPOINT // ptr isa jl_value_t*
{
    mmtk_gc_wb_fast(ptr, (void*)0);
}

STATIC_INLINE void jl_gc_multi_wb(const void *parent, const jl_value_t *ptr) JL_NOTSAFEPOINT
{
    mmtk_gc_wb_fast(parent, (void*)0);
}

STATIC_INLINE void jl_gc_wb_genericmemory_copy_boxed(const jl_value_t *dest_owner, _Atomic(void*) ** dest_pp,
                                          jl_genericmemory_t *src, _Atomic(void*) ** src_pp,
                                          size_t* n) JL_NOTSAFEPOINT
{
    if (MMTK_NEEDS_WRITE_BARRIER == MMTK_OBJECT_BARRIER) {
        // Same armed check as mmtk_gc_wb_fast, but during marking the SATB
        // capture is sized to the mutation: only the overwritten range's
        // old values are recorded (handed to concurrent workers), instead
        // of the whole-object field iteration that stalled the mutator for
        // O(object) on large arrays.  The object is deliberately NOT
        // logged on this path, so later writes keep capturing their own
        // ranges.  Outside marking the object-granularity remset entry is
        // unchanged.
        intptr_t addr = (intptr_t) (void*) dest_owner;
        uint8_t* meta_addr = (uint8_t*) (MMTK_SIDE_LOG_BIT_BASE_ADDRESS) + (addr >> 6);
        intptr_t shift = (addr >> 3) & 0b111;
        uint8_t byte_val = *meta_addr;
        if (((byte_val >> shift) & 1) == 1) {
            if (MMTK_SATB_MARKING_ACTIVE) {
                jl_task_t *ct = jl_current_task;
                mmtk_gc_wb_slots_pre(&ct->ptls->gc_tls.mmtk_mutator, (void**)*dest_pp, *n);
            }
            else {
                mmtk_gc_wb_fast(dest_owner, (void*)0);
            }
        }
    }
}

STATIC_INLINE void jl_gc_wb_genericmemory_copy_ptr(const jl_value_t *owner, jl_genericmemory_t *src, char* src_p,
                                          size_t n, jl_datatype_t *dt) JL_NOTSAFEPOINT
{
    mmtk_gc_wb_fast(owner, (void*)0);
}


#ifdef __cplusplus
}
#endif

#endif
