use crate::util::Address;

/// Set a range of memory to 0.
pub fn zero(start: Address, len: usize) {
    set(start, 0, len);
}

/// Zero a claimed allocation range.  This doubles as the mutator-side
/// warm-up pass over reuse-distance-cold memory (see the ConcurrentImmix
/// plan constructor); `MMTK_ZERO_MODE=warm` selects a staged variant that
/// software-prefetches one chunk ahead of the store loop -- the same lines
/// the stores would RFO anyway, requested earlier so the fills overlap
/// (no added bandwidth, higher MLP than a plain memset).
/// Write-intent prefetch over a claimed range (MMTK_ZERO_MODE=pw): pulls
/// each line into the local cache in writable state ahead of the
/// allocation stream's stores -- the same RFOs those stores would incur,
/// issued early and overlappable, with no duplicate write stream (unlike
/// zeroing, which writes every line twice).
pub fn prefetchw_claim(start: Address, len: usize) {
    #[cfg(target_arch = "x86_64")]
    {
        let mut p = 0usize;
        while p < len {
            unsafe {
                std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_ET0 }>(
                    (start + p).to_ptr(),
                );
            }
            p += 64;
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let _ = (start, len);
    }
}

pub fn zero_claim(start: Address, len: usize) {
    #[cfg(target_arch = "x86_64")]
    {
        use std::sync::OnceLock;
        static WARM: OnceLock<bool> = OnceLock::new();
        let warm = *WARM
            .get_or_init(|| std::env::var("MMTK_ZERO_MODE").map_or(false, |v| v == "warm"));
        if warm && len >= 4096 && start.is_aligned_to(64) {
            const CHUNK: usize = 2048;
            let mut off = 0usize;
            // Stage the first chunk.
            let mut p = 0usize;
            while p < CHUNK.min(len) {
                unsafe {
                    std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_T0 }>(
                        (start + p).to_ptr(),
                    );
                }
                p += 64;
            }
            while off < len {
                let n = CHUNK.min(len - off);
                // Stage the next chunk while zeroing this one.
                let next = off + CHUNK;
                if next < len {
                    let mut q = next;
                    while q < (next + CHUNK).min(len) {
                        unsafe {
                            std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_T0 }>(
                                (start + q).to_ptr(),
                            );
                        }
                        q += 64;
                    }
                }
                set(start + off, 0, n);
                off += n;
            }
            return;
        }
    }
    zero(start, len);
}

/// Set a range of memory to the given value. Similar to memset.
pub fn set(start: Address, val: u8, len: usize) {
    unsafe {
        std::ptr::write_bytes(start.to_mut_ptr::<u8>(), val, len);
    }
}
