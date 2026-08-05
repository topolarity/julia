use mmtk::memory_manager;
use mmtk::util::Address;
use mmtk::util::ObjectReference;
use mmtk::vm::ObjectTracer;
use mmtk::vm::VMBinding;
use mmtk::Mutator;

use crate::JuliaVM;

use crate::arraylist_grow;
use crate::jl_gc_get_have_pending_finalizers;
use crate::jl_gc_get_marked_finalizers_list;
use crate::jl_gc_get_thread_finalizer_list;
use crate::jl_gc_get_to_finalize_list;

// Entries in the thread-local and marked finalizer lists may have tagged object
// pointers. These must match the `GC_FIN_*` defines in gc-common.h.
/// The paired finalizer is an unboxed c function pointer.
pub const GC_FIN_CFUNC_TAG: usize = 0x1;
/// The object pointer is a c object pointer, not a `jl_value_t *`.  It must
/// have alignment >= 4 and will be finalized at the next quiescent period.
pub const GC_FIN_COBJ_TAG: usize = 0x2;
/// All bits used to tag finalizer list entries.
pub const GC_FIN_TAG_MASK: usize = GC_FIN_CFUNC_TAG | GC_FIN_COBJ_TAG;

/// Diagnostic (MMTK_FIN_STATS=1): per-pause finalizer-sweep accounting.
fn fin_stats_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("MMTK_FIN_STATS").is_some())
}

/// This is a Rust implementation of finalizer scanning in _jl_gc_collect() in gc.c
pub fn scan_finalizers_in_rust<T: ObjectTracer>(tracer: &mut T) {
    use crate::mmtk::vm::ActivePlan;
    let to_finalize = ArrayListT::to_finalize_list();
    let marked_finalizers_list = ArrayListT::marked_finalizers_list();
    let jl_gc_have_pending_finalizers: *mut i32 = unsafe { jl_gc_get_have_pending_finalizers() };

    // Current length of marked list: we only need to trace objects after this length if this is a nursery GC.
    let mut orig_marked_len = marked_finalizers_list.len;

    let stats = fin_stats_enabled();
    let (tl_before, tf_before, marked_before) = if stats {
        let mut tl = 0;
        for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
            tl += ArrayListT::thread_local_finalizer_list(mutator).len;
        }
        (tl, to_finalize.len, marked_finalizers_list.len)
    } else {
        (0, 0, 0)
    };

    // CONCURRENT FINALIZER SWEEP (majors): the classification of every
    // registered entry scales with the number of live finalizers (BigInt
    // workloads: millions), so like the memory sweep it runs off-pause.
    // The pause does O(threads) work: steal the thread-local lists and the
    // marked list wholesale and defer a sweep packet.  Nothing is traced
    // in-pause; the packet marks everything it keeps (fins, resurrected
    // dead objects, surviving to_finalize entries) against the stable
    // post-trace mark bits, and reclamation of anything this cycle freed
    // is gated (lazy immix reuse, deferred LOS release) until it is done.
    #[cfg(feature = "concurrentimmix")]
    {
        use crate::mmtk::vm::ActivePlan;
        // Aborted FinalMark: marking incomplete, liveness unknown -- no
        // finalizer processing this pause (retried with the FinalMark).
        if crate::SINGLETON
            .get_plan()
            .concurrent()
            .is_some_and(|p| p.final_mark_aborted())
        {
            return;
        }
        if let Some(plan) = crate::SINGLETON
            .get_plan()
            .concurrent()
            .filter(|p| !p.current_collection_is_user_triggered())
        {
            let nursery = crate::collection::is_current_gc_nursery();
            // CONCURRENT MALLOCED SWEEP: detach the per-thread mallocarray
            // lists here (VMRefClosure stage), strictly before the Release
            // bucket where plan.release() reads the reclaim gate to defer
            // the LOS release -- a later gate-set could let LOS free
            // malloced owners' headers in-pause.
            let malloced = unsafe { crate::jl_gc_mmtk_detach_malloced_memory() };
            let mut stealable = if nursery { 0 } else { marked_finalizers_list.len };
            for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
                stealable += ArrayListT::thread_local_finalizer_list(mutator).len;
            }
            if stealable == 0 && malloced == 0 {
                // Nothing detached anywhere: take the in-pause path (it is
                // O(0) then, and skipping the gate keeps warm reuse
                // unthrottled).
            } else if stealable == 0 {
                // Malloced entries only: defer the sweep packet with empty
                // finalizer lists.
                plan.finalizer_defer_packet(Box::new(ConcurrentFinalizerSweep {
                    lists: Vec::new(),
                    marked: StolenList::Copied(Vec::new()),
                    full: !nursery,
                }));
                return;
            } else {
            let mut lists = Vec::new();
            for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
                lists.push(StolenList::steal(ArrayListT::thread_local_finalizer_list(
                    mutator,
                )));
            }
            // Minors never sweep the marked list, and their to_finalize
            // survivors keep their marks (no chunk-mark clear at minors).
            let marked = if nursery {
                StolenList::Copied(Vec::new())
            } else {
                StolenList::steal(marked_finalizers_list)
            };
            if stats {
                let n: usize = lists.iter().map(|l| l.len()).sum();
                eprintln!(
                    "FINSTAT kind={}-detach tl={} marked={} (deferred)",
                    if nursery { "minor" } else { "major" },
                    n / 2,
                    marked.len() / 2
                );
            }
            plan.finalizer_defer_packet(Box::new(ConcurrentFinalizerSweep {
                lists,
                marked,
                full: !nursery,
            }));
            return;
            }
        }
    }

    // Sweep thread local list: if they are not alive, move to to_finalize.
    for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
        let list = ArrayListT::thread_local_finalizer_list(mutator);
        sweep_finalizer_list(
            list,
            to_finalize,
            Some(marked_finalizers_list),
            jl_gc_have_pending_finalizers,
        );
    }

    let (tl_after_sweep, marked_after_tl) = if stats {
        let mut tl = 0;
        for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
            tl += ArrayListT::thread_local_finalizer_list(mutator).len;
        }
        (tl, marked_finalizers_list.len)
    } else {
        (0, 0)
    };

    // If this is a full heap GC, we also sweep marked list.
    let nursery = crate::collection::is_current_gc_nursery();
    if !nursery {
        sweep_finalizer_list(
            marked_finalizers_list,
            to_finalize,
            None,
            jl_gc_have_pending_finalizers,
        );
        orig_marked_len = 0;
    }

    if stats {
        eprintln!(
            "FINSTAT kind={} tl={}->{} migrated={} marked={}->{} freed={} tf={}->{}",
            if nursery { "minor" } else { "major" },
            tl_before / 2,
            tl_after_sweep / 2,
            (marked_after_tl - marked_before) / 2,
            marked_after_tl / 2,
            marked_finalizers_list.len / 2,
            (to_finalize.len - tf_before) / 2,
            tf_before / 2,
            to_finalize.len / 2,
        );
    }

    // Go through thread local list again and trace objects
    for mutator in <JuliaVM as VMBinding>::VMActivePlan::mutators() {
        let list = ArrayListT::thread_local_finalizer_list(mutator);
        mark_finlist(list, 0, tracer);
    }
    // Trace new objects in marked list
    mark_finlist(marked_finalizers_list, orig_marked_len, tracer);
    // Trace objects in to_finalize (which are just pushed in sweeping thread local list)
    mark_finlist(to_finalize, 0, tracer);
}

/// This maps to arraylist_t in arraylist.h. Defining the type allows us to access the list in Rust.
/// typedef struct {
///     size_t len;
///     size_t max;
///     void **items;
///     void *_space[AL_N_INLINE];
/// } arraylist_t;
#[repr(C)]
struct ArrayListT {
    len: usize,
    max: usize,
    items: *mut Address,
    // There are one more field in the end but we dont use it. So omit it.
}

impl ArrayListT {
    // Some arraylist_t pointers used in finalizer implementation.

    /// ptls->finalizers: new finalizers are registered into this thread local list
    fn thread_local_finalizer_list(mutator: &mut Mutator<JuliaVM>) -> &mut ArrayListT {
        let list = unsafe { jl_gc_get_thread_finalizer_list(mutator.mutator_tls.0 .0) };
        unsafe { &mut *list.to_mut_ptr() }
    }
    /// to_finalize: objects that are dead are in this list waiting for finalization
    fn to_finalize_list<'a>() -> &'a mut ArrayListT {
        let list = unsafe { jl_gc_get_to_finalize_list() };
        unsafe { &mut *list.to_mut_ptr() }
    }
    /// finalizer_list_marked: objects that are alive and traced, thus we do not need to scan them again in future nursery GCs.
    fn marked_finalizers_list<'a>() -> &'a mut ArrayListT {
        let list = unsafe { jl_gc_get_marked_finalizers_list() };
        unsafe { &mut *list.to_mut_ptr() }
    }

    fn get(&self, i: usize) -> Address {
        debug_assert!(i < self.len);
        unsafe { *self.items.add(i) }
    }
    fn set(&mut self, i: usize, val: Address) {
        debug_assert!(i < self.len);
        unsafe { *self.items.add(i) = val }
    }
    fn push(&mut self, val: Address) {
        self.grow(1);
        self.set(self.len - 1, val);
    }
    fn grow(&mut self, n: usize) {
        let newlen = self.len + n;
        if newlen > self.max {
            // Call into C to grow the list.
            unsafe {
                arraylist_grow(Address::from_mut_ptr(self as _), n);
            }
        }
        self.len = newlen
    }
}

fn gc_ptr_clear_tag(addr: Address, tag: usize) -> Address {
    let addr = unsafe { Address::from_usize(addr & !tag) };
    debug_assert!(!addr.is_zero());
    addr
}

pub fn gc_ptr_tag(addr: Address, tag: usize) -> bool {
    addr & tag != 0
}

// sweep_finalizer_list in gc.c
fn sweep_finalizer_list(
    list: &mut ArrayListT,
    to_finalize: &mut ArrayListT,
    // finalizer_list_marked is None if list (1st parameter) is finalizer_list_marked.
    // Rust does not allow sending the same mutable reference as two different arguments (cannot borrow __ as mutable more than once at a time)
    mut finalizer_list_marked: Option<&mut ArrayListT>,
    jl_gc_have_pending_finalizers: *mut i32,
) {
    if list.len == 0 {
        return;
    }

    let mut i = 0;
    let mut j = 0;
    while i < list.len {
        let v0: Address = list.get(i);
        let v = unsafe {
            ObjectReference::from_raw_address_unchecked(gc_ptr_clear_tag(v0, GC_FIN_TAG_MASK))
        };
        if v0.is_zero() {
            i += 2;
            // remove from this list
            continue;
        }

        let fin = list.get(i + 1);
        let (isfreed, isold) = if gc_ptr_tag(v0, GC_FIN_COBJ_TAG) {
            (true, false)
        } else {
            let isfreed = !memory_manager::is_live_object(v);
            let isold = finalizer_list_marked.is_some() && !isfreed;
            (isfreed, isold)
        };
        if isfreed || isold {
            // remove from this list
        } else {
            if j < i {
                list.set(j, list.get(i));
                list.set(j + 1, list.get(i + 1));
            }
            j += 2;
        }
        if isfreed {
            to_finalize.push(v0);
            to_finalize.push(fin);
            unsafe {
                *jl_gc_have_pending_finalizers = 1;
            }
        }
        if isold {
            let finalizer_list_marked = finalizer_list_marked.as_mut().unwrap();
            finalizer_list_marked.push(v0);
            finalizer_list_marked.push(fin);
        }
        i += 2;
    }

    list.len = j;
}

// gc_mark_finlist in gc.c
fn mark_finlist<T: ObjectTracer>(list: &mut ArrayListT, start: usize, tracer: &mut T) {
    if list.len <= start {
        return;
    }

    let mut i = start;
    while i < list.len {
        let cur = list.get(i);
        let cur_i = i;
        let mut cur_tag: usize = 0;

        if cur.is_zero() {
            i += 1;
            continue;
        }

        let new_obj_addr = if gc_ptr_tag(cur, GC_FIN_CFUNC_TAG) {
            // Skip next
            i += 1;
            debug_assert!(i < list.len);
            cur_tag = GC_FIN_CFUNC_TAG;
            gc_ptr_clear_tag(cur, GC_FIN_CFUNC_TAG)
        } else {
            // unsafe: We checked `cur.is_zero()` before.
            cur
        };
        if gc_ptr_tag(cur, GC_FIN_COBJ_TAG) {
            i += 1;
            continue;
        }

        let new_obj = unsafe { ObjectReference::from_raw_address_unchecked(new_obj_addr) };

        let traced = tracer.trace_object(new_obj);
        // if object has moved, update the list applying the tag
        list.set(cur_i, unsafe {
            Address::from_usize(traced.to_raw_address() | cur_tag)
        });

        i += 1;
    }
}


/// A thread-local finalizer list (or the marked list) detached from its
/// C `arraylist_t` during a major pause.  Large lists steal the malloc'd
/// buffer (freed after the sweep); short inline-storage lists are copied.
enum StolenList {
    Owned { items: *mut Address, len: usize },
    Copied(Vec<Address>),
}

// The buffers are only touched by the single deferred sweep packet.
unsafe impl Send for StolenList {}

impl StolenList {
    /// `arraylist_t` layout: len, max, items, then `_space[AL_N_INLINE]`
    /// inline storage.  `items` points at `_space` while the list is small.
    const SPACE_OFFSET: usize = 24;
    const AL_N_INLINE: usize = 29;

    fn steal(list: &mut ArrayListT) -> StolenList {
        let inline_space =
            unsafe { (list as *mut ArrayListT as *mut u8).add(Self::SPACE_OFFSET) }
                as *mut Address;
        let len = list.len;
        let stolen = if std::ptr::eq(list.items, inline_space) {
            let mut v = Vec::with_capacity(len);
            for i in 0..len {
                v.push(unsafe { *list.items.add(i) });
            }
            StolenList::Copied(v)
        } else {
            let items = list.items;
            list.items = inline_space;
            list.max = Self::AL_N_INLINE;
            StolenList::Owned { items, len }
        };
        list.len = 0;
        stolen
    }

    fn len(&self) -> usize {
        match self {
            StolenList::Owned { len, .. } => *len,
            StolenList::Copied(v) => v.len(),
        }
    }

    fn entries(&self) -> &[Address] {
        match self {
            StolenList::Owned { items, len } => unsafe {
                std::slice::from_raw_parts(*items, *len)
            },
            StolenList::Copied(v) => v.as_slice(),
        }
    }

    fn free(self) {
        if let StolenList::Owned { items, .. } = self {
            unsafe { libc::free(items as *mut libc::c_void) };
        }
    }
}

/// Deferred sweep of the detached finalizer lists.  Runs post-pause; the
/// all-parked rendezvous guarantees completion before the next pause, so
/// the mark bits are stable and no ClearChunkMarks can intervene.
pub struct ConcurrentFinalizerSweep {
    lists: Vec<StolenList>,
    marked: StolenList,
    /// Major collection: sweep the marked list and re-mark to_finalize
    /// survivors (their marks were erased by this cycle's chunk clear).
    full: bool,
}

impl ConcurrentFinalizerSweep {
    /// Mark `object` and everything reachable from it that reclamation
    /// could otherwise free.  The subgraph is intact: the mutator cannot
    /// reach dead objects, immix reuse is gated, and the LOS release is
    /// deferred behind this packet.  Dead tasks are marked but not
    /// descended: their stacks were already swept in-pause.
    fn resurrect(plan: &dyn mmtk::plan::ConcurrentPlan<VM = JuliaVM>, root: ObjectReference) {
        struct Visitor<'a> {
            plan: &'a dyn mmtk::plan::ConcurrentPlan<VM = JuliaVM>,
            stack: &'a mut Vec<ObjectReference>,
        }
        impl mmtk::vm::SlotVisitor<crate::slots::JuliaVMSlot> for Visitor<'_> {
            fn visit_slot(&mut self, slot: crate::slots::JuliaVMSlot) {
                use crate::mmtk::vm::slot::Slot;
                let obj = match slot {
                    crate::slots::JuliaVMSlot::Simple(se) => se.load(),
                    crate::slots::JuliaVMSlot::Offset(oe) => oe.load(),
                };
                if let Some(obj) = obj {
                    if self.plan.finalizer_resurrect_object(obj) {
                        self.stack.push(obj);
                    }
                }
            }
        }
        let mut stack = Vec::new();
        if plan.finalizer_resurrect_object(root) {
            stack.push(root);
        }
        while let Some(obj) = stack.pop() {
            let addr = obj.to_raw_address();
            if unsafe { crate::julia_scanning::mmtk_jl_typeof(addr) }
                == unsafe { crate::julia_scanning::jl_task_type }
            {
                continue;
            }
            let mut visitor = Visitor {
                plan,
                stack: &mut stack,
            };
            unsafe { crate::julia_scanning::scan_julia_object(addr, &mut visitor) };
        }
    }

    fn sweep_entries(
        plan: &dyn mmtk::plan::ConcurrentPlan<VM = JuliaVM>,
        entries: &[Address],
        out_finalize: &mut Vec<(Address, Address)>,
        out_marked: &mut Vec<(Address, Address)>,
    ) {
        let mut i = 0;
        while i + 1 < entries.len() {
            let v0 = entries[i];
            if v0.is_zero() {
                i += 2;
                continue;
            }
            let fin = entries[i + 1];
            i += 2;
            // The fin slot is an object (a Julia function) unless the entry
            // is tagged; it is reachable only through this list, so keep it.
            if !gc_ptr_tag(v0, GC_FIN_TAG_MASK) && !fin.is_zero() {
                Self::resurrect(plan, unsafe {
                    ObjectReference::from_raw_address_unchecked(fin)
                });
            }
            if gc_ptr_tag(v0, GC_FIN_COBJ_TAG) {
                out_finalize.push((v0, fin));
                continue;
            }
            let v = unsafe {
                ObjectReference::from_raw_address_unchecked(gc_ptr_clear_tag(v0, GC_FIN_TAG_MASK))
            };
            if memory_manager::is_live_object(v) {
                out_marked.push((v0, fin));
            } else {
                Self::resurrect(plan, v);
                out_finalize.push((v0, fin));
            }
        }
    }
}

impl mmtk::scheduler::GCWork<JuliaVM> for ConcurrentFinalizerSweep {
    fn do_work(
        &mut self,
        _worker: &mut mmtk::scheduler::GCWorker<JuliaVM>,
        mmtk: &'static mmtk::MMTK<JuliaVM>,
    ) {
        let plan = mmtk.get_plan().concurrent().unwrap();

        // Surviving to_finalize entries were resurrected when queued, but
        // this cycle's chunk-mark clear erased that: re-mark them.  Snapshot
        // under the finalizers lock (the mutator drains this list).
        let snapshot: Vec<(Address, Address)> = if self.full {
            unsafe { crate::jl_gc_mmtk_finalizers_lock() };
            let to_finalize = ArrayListT::to_finalize_list();
            let mut v = Vec::with_capacity(to_finalize.len);
            let mut i = 0;
            while i + 1 < to_finalize.len {
                v.push((to_finalize.get(i), to_finalize.get(i + 1)));
                i += 2;
            }
            unsafe { crate::jl_gc_mmtk_finalizers_unlock() };
            v
        } else {
            Vec::new()
        };
        for (v0, fin) in snapshot {
            if v0.is_zero() {
                continue;
            }
            if !gc_ptr_tag(v0, GC_FIN_TAG_MASK) && !fin.is_zero() {
                Self::resurrect(plan, unsafe {
                    ObjectReference::from_raw_address_unchecked(fin)
                });
            }
            if !gc_ptr_tag(v0, GC_FIN_COBJ_TAG) {
                let v = unsafe {
                    ObjectReference::from_raw_address_unchecked(gc_ptr_clear_tag(
                        v0,
                        GC_FIN_TAG_MASK,
                    ))
                };
                Self::resurrect(plan, v);
            }
        }

        // Classify the detached entries (no lock needed: the lists are ours
        // and marking is idempotent).
        let mut out_finalize: Vec<(Address, Address)> = Vec::new();
        let mut out_marked: Vec<(Address, Address)> = Vec::new();
        for list in &self.lists {
            Self::sweep_entries(plan, list.entries(), &mut out_finalize, &mut out_marked);
        }
        Self::sweep_entries(plan, self.marked.entries(), &mut out_finalize, &mut out_marked);

        // Publish results.  NOTE: an explicit `finalize(x)` racing this
        // window cannot see detached entries and returns without running
        // them; they run via to_finalize shortly after instead.
        {
            unsafe { crate::jl_gc_mmtk_finalizers_lock() };
            let to_finalize = ArrayListT::to_finalize_list();
            let marked = ArrayListT::marked_finalizers_list();
            for (v0, fin) in &out_marked {
                marked.push(*v0);
                marked.push(*fin);
            }
            let have_pending: *mut i32 = unsafe { jl_gc_get_have_pending_finalizers() };
            if !out_finalize.is_empty() {
                for (v0, fin) in &out_finalize {
                    to_finalize.push(*v0);
                    to_finalize.push(*fin);
                }
                unsafe { *have_pending = 1 };
            }
            unsafe { crate::jl_gc_mmtk_finalizers_unlock() };
        }

        for list in std::mem::take(&mut self.lists) {
            list.free();
        }
        StolenList::free(std::mem::replace(
            &mut self.marked,
            StolenList::Copied(Vec::new()),
        ));

        // Concurrent malloced-memory sweep (detached in-pause), then the
        // deferred LOS release, then lift the reuse gate.
        unsafe { crate::jl_gc_mmtk_sweep_malloced_memory_detached() };
        memory_manager::concurrent_finalizer_los_release(mmtk, self.full);
        plan.finalizer_sweep_done();
    }
}
