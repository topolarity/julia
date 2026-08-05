// All functions here are extern function. There is no point for marking them as unsafe.
#![allow(clippy::not_unsafe_ptr_arg_deref)]
use crate::JuliaVM;
use crate::JULIA_HEADER_SIZE;
use crate::MMTK_SIDE_LOG_BIT_BASE_ADDRESS;
use crate::SINGLETON;
use crate::{BUILDER, DISABLED_GC, MUTATORS, USER_TRIGGERED_GC};

use libc::c_char;
use log::*;
use mmtk::memory_manager;
use mmtk::scheduler::GCWorker;
use mmtk::util::api_util::NullableObjectReference;
use mmtk::util::opaque_pointer::*;
use mmtk::util::{Address, ObjectReference, OpaquePointer};
use mmtk::AllocationSemantics;
use mmtk::Mutator;
use std::ffi::CStr;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

#[no_mangle]
pub extern "C" fn mmtk_gc_init(
    min_heap_size: usize,
    max_heap_size: usize,
    n_gcthreads: usize,
    header_size: usize,
    buffer_tag: usize,
) {
    unsafe {
        crate::JULIA_HEADER_SIZE = header_size;
        crate::JULIA_BUFF_TAG = buffer_tag;
    };

    // We don't need the env var, as we will overwrite the plan with the defined feature.
    std::env::remove_var("MMTK_PLAN");

    {
        let mut builder = BUILDER.lock().unwrap();

        // Set plan
        use mmtk::util::options::PlanSelector;
        let force_plan = if cfg!(feature = "nogc") {
            Some(PlanSelector::NoGC)
        } else if cfg!(feature = "marksweep") {
            Some(PlanSelector::MarkSweep)
        } else if cfg!(feature = "immix") {
            Some(PlanSelector::Immix)
        } else if cfg!(feature = "stickyimmix") {
            Some(PlanSelector::StickyImmix)
        } else if cfg!(feature = "concurrentimmix") {
            Some(PlanSelector::ConcurrentImmix)
        } else {
            None
        };
        if let Some(plan) = force_plan {
            builder.options.plan.set(plan);
        }

        // Set heap size
        let success =
            // By default min and max heap size are 0, and we use the Stock GC heuristics
            if min_heap_size == 0 && max_heap_size == 0 {
                info!(
                    "Setting mmtk heap size to use Stock GC heuristics as defined in gc_trigger.rs",
                );
                builder
                    .options
                    .gc_trigger
                    .set(mmtk::util::options::GCTriggerSelector::Delegated)
            } else if min_heap_size != 0 {
                info!(
                    "Setting mmtk heap size to a variable size with min-max of {}-{} (in bytes)",
                    min_heap_size, max_heap_size
                );
                builder.options.gc_trigger.set(
                    mmtk::util::options::GCTriggerSelector::DynamicHeapSize(
                        min_heap_size,
                        max_heap_size,
                    ),
                )
            } else {
                info!(
                    "Setting mmtk heap size to a fixed max of {} (in bytes)",
                    max_heap_size
                );
                builder.options.gc_trigger.set(
                    mmtk::util::options::GCTriggerSelector::FixedHeapSize(max_heap_size),
                )
            };
        assert!(
            success,
            "Failed to set heap size to {}-{}",
            min_heap_size, max_heap_size
        );

        // Set using weak references
        let success = builder.options.no_reference_types.set(false);
        assert!(success, "Failed to set no_reference_types to false");

        // Set GC threads
        if n_gcthreads > 0 {
            let success = builder.options.threads.set(n_gcthreads);
            assert!(success, "Failed to set GC threads to {}", n_gcthreads);
        }
    }

    // Make sure that we haven't initialized MMTk (by accident) yet
    assert!(!crate::MMTK_INITIALIZED.load(Ordering::SeqCst));
    // Make sure we initialize MMTk here
    lazy_static::initialize(&SINGLETON);

    unsafe {
        MMTK_SIDE_LOG_BIT_BASE_ADDRESS =
            mmtk::util::metadata::side_metadata::global_side_metadata_vm_base_address();
    }

    // DIAG (MMTK_WATCH_MARK_EARLY): publish the watch address at the earliest
    // possible moment (right after metadata layout init) to catch the
    // boot-time 0xFF writer.
    if std::env::var_os("MMTK_WATCH_MARK_EARLY").is_some() {
        use mmtk::vm::ObjectModel;
        if let mmtk::util::metadata::MetadataSpec::OnSide(side) =
            *<JuliaVM as mmtk::vm::VMBinding>::VMObjectModel::LOCAL_MARK_BIT_SPEC
        {
            let chunk = unsafe { Address::from_usize(0x200bcc00000usize) };
            let meta =
                mmtk::util::metadata::side_metadata::helpers::address_to_meta_address(&side, chunk);
            unsafe { MMTK_DEBUG_WATCH_ADDR = meta.as_usize() };
            eprintln!("[watch-mark-early] meta addr = {:?}", meta);
            unsafe { libc::raise(libc::SIGTRAP) };
        }
    }

    // Hijack the panic hook to make sure that if we crash in the GC threads, the process aborts.
    crate::set_panic_hook();

    // Assert to make sure our fastpath allocation is correct.
    {
        // If the assertion failed, check the allocation fastpath in Julia
        // - runtime fastpath: mmtk_immix_alloc_fast and mmtk_immortal_alloc_fast in julia.h
        // - compiler inserted fastpath: llvm-final-gc-lowering.cpp
        use mmtk::util::alloc::AllocatorSelector;
        let default_allocator = memory_manager::get_allocator_mapping::<JuliaVM>(
            &SINGLETON,
            AllocationSemantics::Default,
        );
        assert_eq!(default_allocator, AllocatorSelector::Immix(0));
        let immortal_allocator = memory_manager::get_allocator_mapping::<JuliaVM>(
            &SINGLETON,
            AllocationSemantics::Immortal,
        );
        assert_eq!(immortal_allocator, AllocatorSelector::BumpPointer(0));
    }

    // Assert to make sure alignment used in C is correct
    {
        // If the assertion failed, check MMTK_MIN_ALIGNMENT in julia.h
        assert_eq!(<JuliaVM as mmtk::vm::VMBinding>::MIN_ALIGNMENT, 4);
    }
}

#[no_mangle]
pub extern "C" fn mmtk_bind_mutator(tls: VMMutatorThread, tid: usize) -> *mut Mutator<JuliaVM> {
    let mutator_box = memory_manager::bind_mutator(&SINGLETON, tls);

    let res = Box::into_raw(mutator_box);

    info!("Binding mutator {:?} to thread id = {}", res, tid);
    res
}

#[no_mangle]
pub extern "C" fn mmtk_post_bind_mutator(
    mutator: *mut Mutator<JuliaVM>,
    original_box_mutator: *mut Mutator<JuliaVM>,
) {
    // We have to store the original boxed mutator. Otherwise, we may have dangling pointers in mutator.
    MUTATORS.write().unwrap().insert(
        Address::from_mut_ptr(mutator),
        Address::from_mut_ptr(original_box_mutator),
    );
}

#[no_mangle]
pub extern "C" fn mmtk_destroy_mutator(mutator: *mut Mutator<JuliaVM>) {
    // destroy the mutator with MMTk.
    memory_manager::destroy_mutator(unsafe { &mut *mutator });

    let mut mutators = MUTATORS.write().unwrap();
    let key = Address::from_mut_ptr(mutator);

    // Clear the original boxed mutator
    let orig_mutator = mutators.get(&key).unwrap();
    let _ = unsafe { Box::from_raw(orig_mutator.to_mut_ptr::<Mutator<JuliaVM>>()) };

    // Remove from our hashmap
    mutators.remove(&key);
}

#[no_mangle]
pub extern "C" fn mmtk_notify_task_resume(
    mutator: *mut Mutator<JuliaVM>,
    task: *const crate::julia_types::_jl_task_t,
) {
    #[cfg(feature = "concurrentimmix")]
    {
        if !crate::collection::CONCURRENT_MARKING_ACTIVE.load(Ordering::SeqCst)
            || task.is_null()
            || mutator.is_null()
        {
            if std::env::var_os("MMTK_SNAP_TRACE").is_some() && !task.is_null() {
                eprintln!(
                    "[snap] HOOK-SKIP task={:#x} marking_flag=false",
                    task as usize
                );
            }
            return;
        }

        crate::scanning::GC_STACK_SNAPSHOTS.resume_barrier_scan_task(task);
    }

    #[cfg(not(feature = "concurrentimmix"))]
    {
        let _ = (mutator, task);
        panic!("mmtk_notify_task_resume should not be called for non-concurrent plans");
    }
}

#[no_mangle]
pub extern "C" fn mmtk_alloc(
    mutator: *mut Mutator<JuliaVM>,
    size: usize,
    align: usize,
    offset: usize,
    semantics: AllocationSemantics,
) -> Address {
    debug_assert!(
        mmtk::util::conversions::raw_is_aligned(
            size,
            <JuliaVM as mmtk::vm::VMBinding>::MIN_ALIGNMENT
        ),
        "Alloc size {} is not aligned to min alignment",
        size
    );
    memory_manager::alloc::<JuliaVM>(unsafe { &mut *mutator }, size, align, offset, semantics)
}

#[no_mangle]
pub extern "C" fn mmtk_alloc_large(
    mutator: *mut Mutator<JuliaVM>,
    size: usize,
    align: usize,
    offset: usize,
) -> Address {
    memory_manager::alloc::<JuliaVM>(
        unsafe { &mut *mutator },
        size,
        align,
        offset,
        AllocationSemantics::Los,
    )
}

#[no_mangle]
pub extern "C" fn mmtk_post_alloc(
    mutator: *mut Mutator<JuliaVM>,
    refer: ObjectReference,
    bytes: usize,
    semantics: AllocationSemantics,
) {
    memory_manager::post_alloc::<JuliaVM>(unsafe { &mut *mutator }, refer, bytes, semantics)
}

#[no_mangle]
pub extern "C" fn mmtk_will_never_move(object: ObjectReference) -> bool {
    !object.is_movable()
}

#[no_mangle]
pub extern "C" fn mmtk_is_moving() -> bool {
    SINGLETON.get_plan().constraints().moves_objects
}

#[no_mangle]
pub extern "C" fn mmtk_get_plan_name() -> *const c_char {
    static PLAN_NAME: std::sync::OnceLock<std::ffi::CString> = std::sync::OnceLock::new();
    PLAN_NAME
        .get_or_init(|| {
            let name = format!("{:?}", *SINGLETON.get_options().plan);
            std::ffi::CString::new(name).unwrap()
        })
        .as_ptr()
}

#[no_mangle]
pub extern "C" fn mmtk_start_worker(tls: VMWorkerThread, worker: *mut GCWorker<JuliaVM>) {
    let worker = unsafe { Box::from_raw(worker) };
    memory_manager::start_worker::<JuliaVM>(&SINGLETON, tls, worker)
}

#[no_mangle]
pub extern "C" fn mmtk_initialize_collection(tls: VMThread) {
    // Diagnostics: report in-pause packets slower than this (ns) to stderr.
    if let Ok(v) = std::env::var("MMTK_PAUSE_PKT_REPORT_NS") {
        if let Ok(ns) = v.parse::<u64>() {
            mmtk::diag::PAUSE_PKT_REPORT_NS.store(ns, Ordering::SeqCst);
        }
    }
    memory_manager::initialize_collection(&SINGLETON, tls);
}

#[no_mangle]
pub extern "C" fn mmtk_used_bytes() -> usize {
    memory_manager::used_bytes(&SINGLETON)
}

#[no_mangle]
pub extern "C" fn mmtk_free_bytes() -> usize {
    memory_manager::free_bytes(&SINGLETON)
}

#[no_mangle]
pub extern "C" fn mmtk_total_bytes() -> usize {
    memory_manager::total_bytes(&SINGLETON)
}

#[no_mangle]
pub extern "C" fn mmtk_is_live_object(object: ObjectReference) -> bool {
    object.is_live()
}

#[no_mangle]
pub extern "C" fn mmtk_is_mapped_address(address: Address) -> bool {
    address.is_mapped()
}

#[no_mangle]
pub extern "C" fn mmtk_handle_user_collection_request(tls: VMMutatorThread, collection: u8) {
    AtomicIsize::fetch_add(&USER_TRIGGERED_GC, 1, Ordering::SeqCst);
    if AtomicBool::load(&DISABLED_GC, Ordering::SeqCst) {
        AtomicIsize::fetch_add(&USER_TRIGGERED_GC, -1, Ordering::SeqCst);
        return;
    }
    // See jl_gc_collection_t
    match collection {
        // auto
        0 => memory_manager::handle_user_collection_request::<JuliaVM>(&SINGLETON, tls),
        // full
        1 => SINGLETON.handle_user_collection_request(tls, true, true),
        // incremental
        2 => SINGLETON.handle_user_collection_request(tls, true, false),
        _ => unreachable!(),
    };
}

#[no_mangle]
pub extern "C" fn mmtk_add_weak_candidate(reff: ObjectReference) {
    memory_manager::add_weak_candidate(&SINGLETON, reff)
}

#[no_mangle]
pub extern "C" fn mmtk_add_soft_candidate(reff: ObjectReference) {
    memory_manager::add_soft_candidate(&SINGLETON, reff)
}

#[no_mangle]
pub extern "C" fn mmtk_add_phantom_candidate(reff: ObjectReference) {
    memory_manager::add_phantom_candidate(&SINGLETON, reff)
}

#[no_mangle]
pub extern "C" fn mmtk_harness_begin(tls: VMMutatorThread) {
    memory_manager::harness_begin(&SINGLETON, tls)
}

#[no_mangle]
pub extern "C" fn mmtk_harness_end(_tls: OpaquePointer) {
    memory_manager::harness_end(&SINGLETON)
}

#[no_mangle]
pub extern "C" fn mmtk_process(name: *const c_char, value: *const c_char) -> bool {
    let name_str: &CStr = unsafe { CStr::from_ptr(name) };
    let value_str: &CStr = unsafe { CStr::from_ptr(value) };
    let mut builder = BUILDER.lock().unwrap();
    memory_manager::process(
        &mut builder,
        name_str.to_str().unwrap(),
        value_str.to_str().unwrap(),
    )
}

#[no_mangle]
pub extern "C" fn mmtk_starting_heap_address() -> Address {
    memory_manager::starting_heap_address()
}

#[no_mangle]
pub extern "C" fn mmtk_last_heap_address() -> Address {
    memory_manager::last_heap_address()
}

// Accessed from C to count the bytes we allocated with jl_gc_counted_malloc etc.
#[no_mangle]
pub static JULIA_MALLOC_BYTES: AtomicUsize = AtomicUsize::new(0);

#[no_mangle]
pub extern "C" fn mmtk_gc_poll(tls: VMMutatorThread) {
    memory_manager::gc_poll(&SINGLETON, tls);
}

#[no_mangle]
pub extern "C" fn mmtk_notify_collections_enabled() {
    memory_manager::notify_collections_enabled(&SINGLETON);
}

#[no_mangle]
pub extern "C" fn mmtk_gc_request_pending() -> u8 {
    memory_manager::is_gc_request_pending(&SINGLETON) as u8
}

#[no_mangle]
pub extern "C" fn mmtk_runtime_panic() {
    panic!("Panicking at runtime!")
}

#[no_mangle]
pub extern "C" fn mmtk_unreachable() {
    unreachable!()
}

/// DIAG: address for gdb hardware watchpoint (see MMTK_WATCH_MARK).
#[no_mangle]
pub static mut MMTK_DEBUG_WATCH_ADDR: usize = 0;

#[no_mangle]
#[allow(mutable_transmutes)]
pub extern "C" fn mmtk_set_vm_space(start: Address, size: usize) {
    // DIAG (MMTK_WATCH_MARK): compute the object-mark metadata address for
    // the (deterministic) first immix chunk, publish it for gdb, and trap so
    // a script can arm a hardware watchpoint before the corruption happens.
    if std::env::var_os("MMTK_WATCH_MARK").is_some() {
        use mmtk::vm::ObjectModel;
        if let mmtk::util::metadata::MetadataSpec::OnSide(side) =
            *<JuliaVM as mmtk::vm::VMBinding>::VMObjectModel::LOCAL_MARK_BIT_SPEC
        {
            let chunk = unsafe { Address::from_usize(0x200bcc00000usize) };
            let meta =
                mmtk::util::metadata::side_metadata::helpers::address_to_meta_address(&side, chunk);
            unsafe { MMTK_DEBUG_WATCH_ADDR = meta.as_usize() };
            eprintln!("[watch-mark] meta addr for chunk 0x200bcc00000 = {:?}", meta);
            unsafe { libc::raise(libc::SIGTRAP) };
        }
    }
    let mmtk: &mmtk::MMTK<JuliaVM> = &SINGLETON;
    let mmtk_mut: &mut mmtk::MMTK<JuliaVM> = unsafe { std::mem::transmute(mmtk) };
    memory_manager::set_vm_space(mmtk_mut, start, size);

    #[cfg(feature = "stickyimmix")]
    set_side_log_bit_for_region(start, size);
}

#[no_mangle]
pub extern "C" fn mmtk_memory_region_copy(
    mutator: *mut Mutator<JuliaVM>,
    src_obj: ObjectReference,
    src_addr: Address,
    dst_obj: ObjectReference,
    dst_addr: Address,
    count: usize,
) {
    use crate::slots::JuliaMemorySlice;
    let src = JuliaMemorySlice {
        owner: src_obj,
        start: src_addr,
        count,
    };
    let dst = JuliaMemorySlice {
        owner: dst_obj,
        start: dst_addr,
        count,
    };
    let mutator = unsafe { &mut *mutator };
    memory_manager::memory_region_copy(mutator, src, dst);
}

#[no_mangle]
#[allow(unused_variables)] // Args are only used for sticky immix.
pub extern "C" fn mmtk_immortal_region_post_alloc(start: Address, size: usize) {
    #[cfg(feature = "stickyimmix")]
    set_side_log_bit_for_region(start, size);
}

#[cfg(feature = "stickyimmix")]
fn set_side_log_bit_for_region(start: Address, size: usize) {
    debug!("Bulk set {} to {} ({} bytes)", start, start + size, size);
    use crate::mmtk::vm::ObjectModel;
    match <JuliaVM as mmtk::vm::VMBinding>::VMObjectModel::GLOBAL_LOG_BIT_SPEC.as_spec() {
        mmtk::util::metadata::MetadataSpec::OnSide(side) => side.bset_metadata(start, size),
        _ => unimplemented!(),
    }
}

#[no_mangle]
pub extern "C" fn mmtk_object_reference_write_pre(
    mutator: *mut Mutator<JuliaVM>,
    src: ObjectReference,
    target: NullableObjectReference,
) {
    let mutator = unsafe { &mut *mutator };
    memory_manager::object_reference_write_pre(
        mutator,
        src,
        crate::slots::JuliaVMSlot::Simple(mmtk::vm::slot::SimpleSlot::from_address(Address::ZERO)),
        target.into(),
    )
}

#[no_mangle]
pub extern "C" fn mmtk_object_reference_write_post(
    mutator: *mut Mutator<JuliaVM>,
    src: ObjectReference,
    target: NullableObjectReference,
) {
    let mutator = unsafe { &mut *mutator };
    memory_manager::object_reference_write_post(
        mutator,
        src,
        crate::slots::JuliaVMSlot::Simple(mmtk::vm::slot::SimpleSlot::from_address(Address::ZERO)),
        target.into(),
    )
}

#[no_mangle]
pub extern "C" fn mmtk_object_reference_write_slow(
    mutator: &'static mut Mutator<JuliaVM>,
    src: ObjectReference,
    target: NullableObjectReference,
) {
    use mmtk::MutatorContext;
    mutator.barrier().object_reference_write_slow(
        src,
        crate::slots::JuliaVMSlot::Simple(mmtk::vm::slot::SimpleSlot::from_address(Address::ZERO)),
        target.into(),
    );
}

#[no_mangle]
pub extern "C" fn mmtk_object_is_managed_by_mmtk(addr: usize) -> bool {
    crate::api::mmtk_is_mapped_address(unsafe { Address::from_usize(addr) })
}

#[no_mangle]
pub extern "C" fn mmtk_start_spawned_worker_thread(
    tls: VMWorkerThread,
    ctx: *mut GCWorker<JuliaVM>,
) {
    mmtk_start_worker(tls, ctx);
}

#[inline(always)]
pub fn store_obj_size(obj: ObjectReference, size: usize) {
    let addr_size = obj.to_raw_address() - 16;
    unsafe {
        addr_size.store::<u64>(size as u64);
    }
}

#[no_mangle]
pub extern "C" fn mmtk_store_obj_size_c(obj: ObjectReference, size: usize) {
    let addr_size = obj.to_raw_address() - 16;
    unsafe {
        addr_size.store::<u64>(size as u64);
    }
}

#[no_mangle]
pub extern "C" fn mmtk_get_obj_size(obj: ObjectReference) -> usize {
    unsafe {
        let addr_size = obj.to_raw_address() - 2 * JULIA_HEADER_SIZE;
        addr_size.load::<u64>() as usize
    }
}

#[cfg(all(feature = "object_pinning", not(feature = "non_moving")))]
#[no_mangle]
pub extern "C" fn mmtk_pin_object(object: ObjectReference) -> bool {
    // We may in the future replace this with a check for the immix space (bound check), which should be much cheaper.
    if mmtk_object_is_managed_by_mmtk(object.to_raw_address().as_usize()) {
        memory_manager::pin_object(object)
    } else {
        debug!("Object is not managed by mmtk - (un)pinning it via this function isn't supported.");
        false
    }
}

#[cfg(all(feature = "object_pinning", not(feature = "non_moving")))]
#[no_mangle]
pub extern "C" fn mmtk_unpin_object(object: ObjectReference) -> bool {
    if mmtk_object_is_managed_by_mmtk(object.to_raw_address().as_usize()) {
        memory_manager::unpin_object(object)
    } else {
        debug!("Object is not managed by mmtk - (un)pinning it via this function isn't supported.");
        false
    }
}

#[cfg(all(feature = "object_pinning", not(feature = "non_moving")))]
#[no_mangle]
pub extern "C" fn mmtk_is_pinned(object: ObjectReference) -> bool {
    if mmtk_object_is_managed_by_mmtk(object.to_raw_address().as_usize()) {
        memory_manager::is_pinned(object)
    } else {
        debug!("Object is not managed by mmtk - checking via this function isn't supported.");
        false
    }
}

// If the `non-moving` feature is selected, pinning/unpinning is a noop and simply returns false
#[cfg(all(feature = "object_pinning", feature = "non_moving"))]
#[no_mangle]
pub extern "C" fn mmtk_pin_object(_object: ObjectReference) -> bool {
    false
}

#[cfg(all(feature = "object_pinning", feature = "non_moving"))]
#[no_mangle]
pub extern "C" fn mmtk_unpin_object(_object: ObjectReference) -> bool {
    false
}

#[cfg(all(feature = "object_pinning", feature = "non_moving"))]
#[no_mangle]
pub extern "C" fn mmtk_is_pinned(_object: ObjectReference) -> bool {
    false
}

#[no_mangle]
pub extern "C" fn mmtk_set_concurrent_marking_enabled(enabled: bool) {
    #[cfg(feature = "concurrentimmix")]
    {
        let mut builder = BUILDER.lock().unwrap();
        let success = builder
            .options
            .concurrent_immix_disable_concurrent_marking
            .set(!enabled);
        assert!(
            success,
            "Failed to set concurrent_immix_disable_concurrent_marking"
        );
    }
    #[cfg(not(feature = "concurrentimmix"))]
    {
        let _ = enabled;
    }
}

#[no_mangle]
pub extern "C" fn get_mmtk_version() -> *const c_char {
    crate::build_info::MMTK_JULIA_FULL_VERSION_STRING
        .as_c_str()
        .as_ptr() as _
}


#[no_mangle]
pub extern "C" fn mmtk_gc_count_total() -> usize {
    crate::GC_COUNT_TOTAL.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C" fn mmtk_gc_count_emergency() -> usize {
    crate::GC_COUNT_EMERGENCY.load(Ordering::SeqCst)
}

#[no_mangle]
pub extern "C" fn mmtk_gc_count_full() -> usize { crate::GC_COUNT_FULL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_gc_count_initial() -> usize { crate::GC_COUNT_INITIAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_gc_count_final() -> usize { crate::GC_COUNT_FINAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_gc_count_nursery() -> usize { crate::GC_COUNT_NURSERY.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_stw_max_ns() -> u64 { crate::STW_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_stw_total_ns() -> u64 { crate::STW_TOTAL_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_block_max_ns() -> u64 { crate::BLOCK_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_block_total_ns() -> u64 { crate::BLOCK_TOTAL_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_block_count() -> u64 { crate::BLOCK_COUNT.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_reset_gc_stats() {
    crate::STW_MAX_NS.store(0, Ordering::SeqCst);
    crate::STW_TOTAL_NS.store(0, Ordering::SeqCst);
    crate::BLOCK_MAX_NS.store(0, Ordering::SeqCst);
    crate::BLOCK_TOTAL_NS.store(0, Ordering::SeqCst);
    crate::BLOCK_COUNT.store(0, Ordering::SeqCst);
    crate::TRIG_MAX_NS.store(0, Ordering::SeqCst);
    crate::TRIG_TOTAL_NS.store(0, Ordering::SeqCst);
    crate::TRIG_COUNT.store(0, Ordering::SeqCst);
    crate::GC_COUNT_TOTAL.store(0, Ordering::SeqCst);
    crate::GC_COUNT_FULL.store(0, Ordering::SeqCst);
    crate::GC_COUNT_INITIAL.store(0, Ordering::SeqCst);
    crate::GC_COUNT_FINAL.store(0, Ordering::SeqCst);
}

#[no_mangle]
pub extern "C" fn mmtk_trig_max_ns() -> u64 { crate::TRIG_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_trig_total_ns() -> u64 { crate::TRIG_TOTAL_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_trig_count() -> u64 { crate::TRIG_COUNT.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_diag_lat_total_ns() -> u64 { mmtk::diag::LAT_TOTAL_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_lat_max_ns() -> u64 { mmtk::diag::LAT_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_lat_count() -> u64 { mmtk::diag::LAT_COUNT.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_pkts_total() -> u64 { mmtk::diag::PKTS_TOTAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_pkt_ns_total() -> u64 { mmtk::diag::PKT_NS_TOTAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_park_events() -> u64 { mmtk::diag::PARK_EVENTS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_busy_at_req() -> u64 { mmtk::diag::BUSY_AT_REQ_TOTAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_reset() { mmtk::diag::reset() }

#[no_mangle]
pub extern "C" fn mmtk_diag_pkt_max_in_win_ns() -> u64 { mmtk::diag::PKT_MAX_IN_WIN_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_pkt_sum_in_win_ns() -> u64 { mmtk::diag::PKT_SUM_IN_WIN_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_pkt_max_any_ns() -> u64 { mmtk::diag::PKT_MAX_ANY_NS.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_diag_self_triggered() -> u64 { mmtk::diag::SELF_TRIGGERED.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_diag_noreq_parks() -> u64 { mmtk::diag::NOREQ_PARKS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_noreq_conc_some() -> u64 { mmtk::diag::NOREQ_CONCURRENT_SOME.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_noreq_cm_active() -> u64 { mmtk::diag::NOREQ_CM_ACTIVE.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_diag_sweep_ns() -> u64 { mmtk::diag::SWEEP_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_diag_sweep_pkts() -> u64 { mmtk::diag::SWEEP_PKTS.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_diag_triage() -> u64 {
    mmtk::diag::TRIAGE_CHUNKS.load(Ordering::SeqCst) << 48
        | mmtk::diag::TRIAGE_FREED.load(Ordering::SeqCst) << 32
        | mmtk::diag::TRIAGE_POOLED.load(Ordering::SeqCst) << 16
        | mmtk::diag::POOL_POPS.load(Ordering::SeqCst).min(0xffff)
}
#[no_mangle]
pub extern "C" fn mmtk_diag_clean_blocks() -> u64 { mmtk::diag::CLEAN_BLOCKS.load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_stw_kind_ns(k: usize) -> u64 { crate::STW_KIND_NS[k.min(4)].load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_stw_kind_n(k: usize) -> u64 { crate::STW_KIND_N[k.min(4)].load(Ordering::SeqCst) }

#[no_mangle]
pub extern "C" fn mmtk_stw_kind_max_ns(k: usize) -> u64 { crate::STW_KIND_MAX[k.min(4)].load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_stw_kind_max_at(k: usize) -> u64 { crate::STW_KIND_MAX_AT[k.min(4)].load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_reset_kind_stats() {
    for i in 0..5 {
        crate::STW_KIND_NS[i].store(0, Ordering::SeqCst);
        crate::STW_KIND_N[i].store(0, Ordering::SeqCst);
        crate::STW_KIND_MAX[i].store(0, Ordering::SeqCst);
        crate::STW_KIND_MAX_AT[i].store(0, Ordering::SeqCst);
    }
    crate::STOP_WAIT_MAX_NS.store(0, Ordering::SeqCst);
    mmtk::diag::TRIAGE_MAX_NS.store(0, Ordering::SeqCst);
    mmtk::diag::TRIAGE_NS_TOTAL.store(0, Ordering::SeqCst);
    mmtk::diag::UNLOG_MAX_NS.store(0, Ordering::SeqCst);
}

#[no_mangle]
pub extern "C" fn mmtk_stop_wait_max_ns() -> u64 { crate::STOP_WAIT_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_triage_max_ns() -> u64 { mmtk::diag::TRIAGE_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_triage_ns_total() -> u64 { mmtk::diag::TRIAGE_NS_TOTAL.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_unlog_max_ns() -> u64 { mmtk::diag::UNLOG_MAX_NS.load(Ordering::SeqCst) }
#[no_mangle]
pub extern "C" fn mmtk_set_pause_pkt_report_ns(ns: u64) {
    mmtk::diag::PAUSE_PKT_REPORT_NS.store(ns, Ordering::SeqCst);
}

/// EXIT-PATH SUPPORT: whether a deferred concurrent finalizer sweep still
/// holds detached entries.  `jl_gc_run_all_finalizers` harvests the lists
/// wholesale at exit; it must wait until pending sweeps have published
/// their entries back, or finalizers (including the stream flushers) are
/// silently skipped.
#[no_mangle]
pub extern "C" fn mmtk_concurrent_finalizer_sweep_pending() -> i32 {
    match crate::SINGLETON.get_plan().concurrent() {
        Some(plan) if plan.finalizer_sweep_pending() => 1,
        _ => 0,
    }
}

/// RANGE-PRECISE SATB PRE-WRITE BARRIER: capture the old values of exactly
/// the `n` slots about to be overwritten by a bulk write (memmove_refs /
/// copyto! into an old object).  Only meaningful during concurrent marking;
/// the C fast path gates on MMTK_SATB_MARKING_ACTIVE and the owner's unlog
/// bit before calling.  Packets are capped so no single work unit scales
/// beyond the mutation.
#[no_mangle]
pub extern "C" fn mmtk_gc_wb_slots_pre(
    mutator: &'static mut Mutator<JuliaVM>,
    slots: *const Address,
    n: usize,
) {
    use mmtk::util::ObjectReference;
    use mmtk::MutatorContext;
    if n == 0 || !crate::collection::CONCURRENT_MARKING_ACTIVE.load(atomic::Ordering::SeqCst) {
        return;
    }
    for i in 0..n {
        let v = unsafe { *slots.add(i) };
        if let Some(obj) = ObjectReference::from_raw_address(v) {
            mutator.barrier().satb_enqueue_value(obj);
        }
    }
}

/// RANGE-PRECISE SATB for JIT-lowered single-slot stores: during marking,
/// large objects capture only the overwritten slot's old value (handed to
/// concurrent workers) and stay unlogged so every armed write pays O(1);
/// small objects keep the amortized whole-object snapshot + log.
#[no_mangle]
pub extern "C" fn mmtk_object_reference_write_slow_slot(
    mutator: &'static mut Mutator<JuliaVM>,
    src: ObjectReference,
    slot: Address,
) {
    // Largeness must be measured as SCAN cost, not object size: a Julia
    // genericmemory object is a small {length, ptr} header whose separately
    // allocated data the snapshot scan walks -- get_current_size() would
    // classify an 80MB array as tiny and take the whole-object path.
    #[inline]
    fn snapshot_scan_cost(src: ObjectReference) -> usize {
        use mmtk::vm::ObjectModel;
        let addr = src.to_raw_address();
        unsafe {
            let vt = crate::julia_scanning::mmtk_jl_typeof(addr);
            if !vt.is_null()
                && (*vt).name == crate::julia_scanning::jl_genericmemory_typename
            {
                let m = addr.to_ptr::<crate::julia_types::jl_genericmemory_t>();
                return (*m).length as usize * 8;
            }
        }
        crate::object_model::VMObjectModel::get_current_size(src)
    }
    const LARGE_OBJECT_BYTES: usize = 16 * 1024;
    if !slot.is_zero()
        && crate::collection::CONCURRENT_MARKING_ACTIVE.load(atomic::Ordering::SeqCst)
        && snapshot_scan_cost(src) > LARGE_OBJECT_BYTES
    {
        let old = unsafe { slot.load::<Address>() };
        if let Some(obj) = mmtk::util::ObjectReference::from_raw_address(old) {
            // Batched into this mutator's SATB buffer (drained at capacity
            // and by the ragged pre-flush) -- a packet per captured value
            // both flooded the scheduler and let single-value packets with
            // huge transitive scans land in the FinalMark pause.
            use mmtk::MutatorContext;
            mutator.barrier().satb_enqueue_value(obj);
        }
        return;
    }
    use mmtk::MutatorContext;
    mutator.barrier().object_reference_write_slow(
        src,
        crate::slots::JuliaVMSlot::Simple(mmtk::vm::slot::SimpleSlot::from_address(Address::ZERO)),
        None.into(),
    );
}

/// RAGGED PRE-FLUSH mutator poll: called from the allocation slow path and
/// the malloc poll while marking is active (the C side gates on
/// MMTK_SATB_MARKING_ACTIVE, so this is free otherwise).
#[no_mangle]
pub extern "C" fn mmtk_ragged_flush_poll(mutator: &'static mut Mutator<JuliaVM>) {
    thread_local! {
        static LAST_ROUND: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    }
    if let Some(plan) = crate::SINGLETON.get_plan().concurrent() {
        let round = plan.ragged_round_id();
        if round != 0 && LAST_ROUND.with(|c| c.get()) != round {
            LAST_ROUND.with(|c| c.set(round));
            plan.ragged_flush_poll(mutator);
        }
    }
}
