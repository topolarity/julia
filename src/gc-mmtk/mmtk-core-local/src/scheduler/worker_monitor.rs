//! This module contains `WorkerMonitor` and related types.  It purposes includes:
//!
//! -   allowing workers to park,
//! -   letting the last parked worker take action, and
//! -   letting workers and mutators notify workers when workers are given things to do.

use std::sync::Mutex;

use super::{
    worker::WorkerShouldExit,
    worker_goals::{WorkerGoal, WorkerGoals},
};

/// The result type of the `on_last_parked` call-back in `WorkMonitor::park_and_wait`.
/// It decides how many workers should wake up after `on_last_parked`.
pub(crate) enum LastParkedResult {
    /// The last parked worker should wait, too, until more work packets are added.
    ParkSelf,
    /// The last parked worker should unpark and find work packet to do.
    WakeSelf,
    /// Wake up all parked GC workers.
    WakeAll,
    /// PROPORTIONAL WAKEUP: wake up to N workers in total (the last parked
    /// worker counts as one).  Avoids the thundering herd on bucket
    /// transitions whose packet count is far below the worker count; more
    /// workers are woken incrementally by `WorkBucket::add` as packets fan
    /// out.
    WakeN(usize),
}

/// A data structure for synchronizing workers with each other and with mutators.
///
/// Unlike `GCWorkerShared`, there is only one instance of `WorkerMonitor`.
///
/// -   It allows workers to park and unpark.
/// -   It allows mutators to notify workers to schedule a GC.
///
/// PER-WORKER PARKING: workers sleep on their own `std::thread::park` token
/// instead of one shared condvar.  Token semantics make wakes targeted and
/// lossless (an unpark issued before the park makes the park return
/// immediately), eliminating the broadcast serialization through the monitor
/// mutex (glibc wait-morphing requeues condvar waiters onto the mutex, where
/// running workers barge ahead of them -- measured as hundreds of no-progress
/// park/wake oscillations per pause).  The `sync` mutex is still used for
/// state transitions and for `on_last_parked` mutual exclusion, but is never
/// held while sleeping.
pub(crate) struct WorkerMonitor {
    /// The synchronized part.
    sync: Mutex<WorkerMonitorSync>,
    /// SPIN-AT-BARRIER: lock-free wake signal.  Bumped lock-free by wake
    /// sites; a would-be sleeper re-checks it under `sync` after registering,
    /// and wakers acquire `sync` to deliver unparks, which orders the bump
    /// against registration (bump-before-lock => sleeper's under-lock
    /// re-check sees it; bump-after => the waker's `wake_one` finds the
    /// registered sleeper).
    wake_epoch: std::sync::atomic::AtomicU64,
    /// Number of workers currently registered in the sleep registry.  Lets
    /// the hot notify path (every `bucket.add`) skip the mutex entirely when
    /// nobody is actually sleeping -- during pauses, workers spin and this is
    /// zero, so notification costs one atomic load.
    sleeper_count: std::sync::atomic::AtomicUsize,
}

/// The synchronized part of `WorkerMonitor`.
struct WorkerMonitorSync {
    /// Count parked workers.
    parker: WorkerParker,
    /// Current and requested goals.
    goals: WorkerGoals,
    /// Per-worker sleep registry: `Some(handle)` iff that worker is currently
    /// sleeping (registered under the lock before sleeping; the slot is taken
    /// by whoever wakes the worker, or cleared by the worker itself on a
    /// spurious/token return).
    sleeping: Vec<Option<std::thread::Thread>>,
}

impl WorkerMonitorSync {
    /// Wake one sleeping worker.  Returns false if none is sleeping.
    fn wake_one(&mut self, sleeper_count: &std::sync::atomic::AtomicUsize) -> bool {
        for slot in self.sleeping.iter_mut() {
            if let Some(t) = slot.take() {
                sleeper_count.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                t.unpark();
                return true;
            }
        }
        false
    }

    /// Wake every sleeping worker.
    fn wake_all(&mut self, sleeper_count: &std::sync::atomic::AtomicUsize) {
        self.wake_up_to(usize::MAX, sleeper_count);
    }

    /// Wake up to `k` sleeping workers.
    fn wake_up_to(&mut self, k: usize, sleeper_count: &std::sync::atomic::AtomicUsize) {
        let mut woken = 0;
        for slot in self.sleeping.iter_mut() {
            if woken >= k {
                break;
            }
            if let Some(t) = slot.take() {
                sleeper_count.fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
                t.unpark();
                woken += 1;
            }
        }
    }
}

/// PAUSE CREW: maximum number of workers woken by broadcast-style
/// notifications while the world is stopped.  Stage-barrier convergence cost
/// scales with the number of awake participants, and in-pause packet work is
/// small; capping participation gives the measured small-crew pause tails
/// while keeping full parallelism for concurrent phases.  Targeted wakes
/// (designated work) are never capped.
const PAUSE_CREW: usize = 4;

/// This struct counts the number of workers parked and identifies the last parked worker.
struct WorkerParker {
    /// The total number of workers.
    worker_count: usize,
    /// Number of parked workers.
    parked_workers: usize,
}

impl WorkerParker {
    fn new(worker_count: usize) -> Self {
        Self {
            worker_count,
            parked_workers: 0,
        }
    }

    /// Increase the packed-workers counter.
    /// Called before a worker is parked.
    ///
    /// Return true if all the workers are parked.
    fn inc_parked_workers(&mut self) -> bool {
        let old = self.parked_workers;
        debug_assert!(old < self.worker_count);
        let new = old + 1;
        self.parked_workers = new;
        new == self.worker_count
    }

    /// Decrease the packed-workers counter.
    /// Called after a worker is resumed from the parked state.
    fn dec_parked_workers(&mut self) {
        let old = self.parked_workers;
        debug_assert!(old <= self.worker_count);
        debug_assert!(old > 0);
        let new = old - 1;
        self.parked_workers = new;
    }
}

impl WorkerMonitor {
    pub fn new(worker_count: usize) -> Self {
        Self {
            sync: Mutex::new(WorkerMonitorSync {
                parker: WorkerParker::new(worker_count),
                goals: Default::default(),
                sleeping: (0..worker_count).map(|_| None).collect(),
            }),
            wake_epoch: std::sync::atomic::AtomicU64::new(0),
            sleeper_count: std::sync::atomic::AtomicUsize::new(0),
        }
    }

    /// Bump the wake epoch (lock-free).  Paired with the sleeper-count check:
    /// wakers bump the epoch BEFORE loading `sleeper_count`, and sleepers
    /// register (incrementing the count) BEFORE re-checking the epoch, so at
    /// least one side always observes the other (Dekker pattern).
    fn bump_epoch(&self) {
        self.wake_epoch
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    }

    /// Make a request.  Can be called by a mutator to request the workers to work towards the
    /// given `goal`.
    pub fn make_request(&self, goal: WorkerGoal) {
        let mut guard = self.sync.lock().unwrap();
        let newly_requested = guard.goals.set_request(goal);
        if newly_requested {
            crate::diag::REQUEST_NS.store(crate::diag::now_ns(), std::sync::atomic::Ordering::SeqCst);
            crate::diag::REQ_PENDING.store(true, std::sync::atomic::Ordering::SeqCst);
            if matches!(goal, WorkerGoal::Gc) {
                crate::diag::PAUSE_PENDING.store(true, std::sync::atomic::Ordering::SeqCst);
            }
            crate::diag::PKTS_SINCE_REQ.store(0, std::sync::atomic::Ordering::SeqCst);
            let busy = (guard.parker.worker_count - guard.parker.parked_workers) as u64;
            crate::diag::BUSY_AT_REQ_TOTAL.fetch_add(busy, std::sync::atomic::Ordering::SeqCst);
            self.bump_epoch();
            guard.wake_one(&self.sleeper_count);
        }
    }

    /// Wake up workers when more work packets are made available for workers,
    /// or a mutator has requested the GC workers to schedule a GC.
    ///
    /// HOT-PATH: called on every `WorkBucket::add`.  Bumps the epoch
    /// lock-free and takes the mutex ONLY if someone is actually sleeping --
    /// during pauses, workers spin and this is a single atomic op, so packet
    /// fan-out no longer serializes on the monitor mutex.
    pub fn notify_work_available(&self, all: bool) {
        self.bump_epoch();
        if self.sleeper_count.load(std::sync::atomic::Ordering::SeqCst) == 0 {
            return;
        }
        let mut guard = self.sync.lock().unwrap();
        if all {
            // PAUSE CREW: cap broadcast fan-out while the world is stopped.
            let cap = if crate::diag::PAUSE_ACTIVE.load(std::sync::atomic::Ordering::Relaxed) {
                PAUSE_CREW
            } else {
                usize::MAX
            };
            guard.wake_up_to(cap, &self.sleeper_count);
        } else {
            guard.wake_one(&self.sleeper_count);
        }
    }

    /// Wake a specific worker (targeted wake for designated work).
    /// Spinning workers detect their designated work directly via
    /// `spin_check`, so the epoch bump here is belt-and-braces.
    pub fn notify_worker(&self, ordinal: usize) {
        self.bump_epoch();
        if self.sleeper_count.load(std::sync::atomic::Ordering::SeqCst) == 0 {
            return;
        }
        let mut guard = self.sync.lock().unwrap();
        if let Some(t) = guard.sleeping[ordinal].take() {
            self.sleeper_count
                .fetch_sub(1, std::sync::atomic::Ordering::SeqCst);
            t.unpark();
        }
    }

    /// Park a worker and wait on the CondVar `workers_have_anything_to_do`.
    ///
    /// If it is the last worker parked, `on_last_parked` will be called.
    /// The argument of `on_last_parked` is true if `sync.gc_requested` is `true`.
    /// The return value of `on_last_parked` will determine whether this worker and other workers
    /// will wake up or block waiting.
    ///
    /// This function returns `Ok(())` if the current worker should continue working,
    /// or `Err(WorkerShouldExit)` if the current worker should exit now.
    pub fn park_and_wait<F, S>(
        &self,
        ordinal: usize,
        on_last_parked: F,
        spin_check: S,
    ) -> Result<(), WorkerShouldExit>
    where
        F: FnOnce(&mut WorkerGoals) -> LastParkedResult,
        S: Fn() -> bool,
    {
        let mut sync = self.sync.lock().unwrap();

        // Park this worker
        crate::diag::PARK_EVENTS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let all_parked = sync.parker.inc_parked_workers();
        trace!(
            "Worker {} parked.  parked/total: {}/{}.  All parked: {}",
            ordinal,
            sync.parker.parked_workers,
            sync.parker.worker_count,
            all_parked
        );

        let mut should_wait = false;

        if all_parked {
            trace!("Worker {} is the last worker parked.", ordinal);
            let result = on_last_parked(&mut sync.goals);
            match result {
                LastParkedResult::ParkSelf => {
                    should_wait = true;
                }
                LastParkedResult::WakeSelf => {
                    // Continue without waiting.
                }
                LastParkedResult::WakeAll => {
                    self.bump_epoch();
                    let cap = if crate::diag::PAUSE_ACTIVE
                        .load(std::sync::atomic::Ordering::Relaxed)
                    {
                        PAUSE_CREW
                    } else {
                        usize::MAX
                    };
                    sync.wake_up_to(cap, &self.sleeper_count);
                }
                LastParkedResult::WakeN(n) => {
                    self.bump_epoch();
                    // Self counts as one woken worker; cap at the pause crew
                    // while the world is stopped.
                    let mut others = n.saturating_sub(1);
                    if crate::diag::PAUSE_ACTIVE.load(std::sync::atomic::Ordering::Relaxed) {
                        others = others.min(PAUSE_CREW.saturating_sub(1));
                    }
                    sync.wake_up_to(others, &self.sleeper_count);
                }
            }
        } else {
            should_wait = true;
        }

        if should_wait {
            use std::sync::atomic::Ordering;
            // SPIN-AT-BARRIER: during a pause (or with a pause pending), the
            // expected wait at a stage barrier is far below a millisecond, so
            // sleeping here would price every barrier at the OS wakeup-latency
            // distribution (5-30us idle, 1-4ms when the target core is busy --
            // the measured pause tail).  Spin instead, watching the lock-free
            // wake epoch and this worker's own designated queue; fall back to
            // a real sleep on deadline or when the pause window closes.  The
            // worker stays counted as parked while spinning, so all-parked
            // detection and `on_last_parked` exclusion are unchanged (any exit
            // from the spin re-acquires `sync` before proceeding).
            // SLEEP TRANSITION (Dekker with the lock-free notify path):
            // register FIRST (making `sleeper_count` visible), then re-check
            // the epoch.  A waker bumps the epoch before loading the sleeper
            // count, so either we see its bump here and abort the sleep, or
            // it sees our registration and takes the mutex to unpark us.
            // Token semantics additionally close the unlock-to-park window.
            // (A spin-at-barrier phase was prototyped here and REMOVED: with
            // 16 workers, both epoch-watching and direct bucket-polling
            // spinners measurably slowed the pause via cache-line contention
            // against the workers doing real work.  Fewer wake edges beats
            // faster wake edges.)
            let epoch0 = self.wake_epoch.load(Ordering::SeqCst);
            sync.sleeping[ordinal] = Some(std::thread::current());
            self.sleeper_count.fetch_add(1, Ordering::SeqCst);
            if self.wake_epoch.load(Ordering::SeqCst) != epoch0 || spin_check() {
                // Wake raced with registration: abort the sleep.
                if sync.sleeping[ordinal].take().is_some() {
                    self.sleeper_count.fetch_sub(1, Ordering::SeqCst);
                }
            } else {
                drop(sync);
                std::thread::park();
                sync = self.sync.lock().unwrap();
                // Our slot may have been taken (and the count adjusted)
                // by the waker; clear it ourselves on spurious returns.
                if sync.sleeping[ordinal].take().is_some() {
                    self.sleeper_count.fetch_sub(1, Ordering::SeqCst);
                }
            }
        }

        // Unpark this worker.
        sync.parker.dec_parked_workers();
        trace!(
            "Worker {} unparked.  parked/total: {}/{}.",
            ordinal,
            sync.parker.parked_workers,
            sync.parker.worker_count,
        );

        // If the current goal is an exit goal, the worker thread should exit.
        if matches!(
            sync.goals.current(),
            Some(WorkerGoal::Shutdown | WorkerGoal::StopForFork)
        ) {
            return Err(WorkerShouldExit);
        }

        Ok(())
    }

    /// Called when all workers have exited.
    pub fn on_all_workers_exited(&self) {
        let mut sync = self.sync.try_lock().unwrap();
        sync.goals.on_current_goal_completed();
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    };

    use super::WorkerMonitor;

    /// Test if the `WorkerMonitor::park_and_wait` method calls the `on_last_parked` callback
    /// properly.
    #[test]
    fn test_last_worker_park_wake_all() {
        let number_threads = 4;
        let worker_monitor = Arc::new(WorkerMonitor::new(number_threads));
        let on_last_parked_called = AtomicUsize::new(0);
        let should_unpark = AtomicBool::new(false);

        std::thread::scope(|scope| {
            for ordinal in 0..number_threads {
                let worker_monitor = worker_monitor.clone();
                let on_last_parked_called = &on_last_parked_called;
                let should_unpark = &should_unpark;
                scope.spawn(move || {
                    // This emulates the use pattern in the scheduler, i.e. checking the condition
                    // ("Is there any work packets available") without holding a mutex.
                    while !should_unpark.load(Ordering::SeqCst) {
                        println!("Thread {} parking...", ordinal);
                        worker_monitor
                            .park_and_wait(ordinal, |_goals| {
                                println!("Thread {} is the last thread parked.", ordinal);
                                on_last_parked_called.fetch_add(1, Ordering::SeqCst);
                                should_unpark.store(true, Ordering::SeqCst);
                                super::LastParkedResult::WakeAll
                            }, || false)
                            .unwrap();
                        println!("Thread {} unparked.", ordinal);
                    }
                });
            }
        });

        // `on_last_parked` should only be called once.
        assert_eq!(on_last_parked_called.load(Ordering::SeqCst), 1);
    }

    /// Like `test_last_worker_park_wake_all`, but only wake up the last parked worker when it
    /// parked.
    #[test]
    fn test_last_worker_park_wake_self() {
        let number_threads = 4;
        let worker_monitor = Arc::new(WorkerMonitor::new(number_threads));
        let on_last_parked_called = AtomicUsize::new(0);
        let threads_running = AtomicUsize::new(0);
        let should_unpark = AtomicBool::new(false);

        std::thread::scope(|scope| {
            for ordinal in 0..number_threads {
                let worker_monitor = worker_monitor.clone();
                let on_last_parked_called = &on_last_parked_called;
                let threads_running = &threads_running;
                let should_unpark = &should_unpark;
                scope.spawn(move || {
                    let mut i_am_the_last_parked_worker = false;
                    // Record the number of threads entering the following `while` loop.
                    threads_running.fetch_add(1, Ordering::SeqCst);
                    while !should_unpark.load(Ordering::SeqCst) {
                        println!("Thread {} parking...", ordinal);
                        worker_monitor
                            .park_and_wait(ordinal, |_goals| {
                                println!("Thread {} is the last thread parked.", ordinal);
                                on_last_parked_called.fetch_add(1, Ordering::SeqCst);
                                should_unpark.store(true, Ordering::SeqCst);
                                i_am_the_last_parked_worker = true;
                                super::LastParkedResult::WakeSelf
                            }, || false)
                            .unwrap();
                        println!("Thread {} unparked.", ordinal);
                    }
                    threads_running.fetch_sub(1, Ordering::SeqCst);

                    if i_am_the_last_parked_worker {
                        println!("The last parked worker woke up");
                        // Only the current worker should wake and leave the `while` loop above.
                        assert_eq!(threads_running.load(Ordering::SeqCst), number_threads - 1);
                        should_unpark.store(true, Ordering::SeqCst);
                        worker_monitor.notify_work_available(true);
                    }
                });
            }
        });

        // `on_last_parked` should only be called once.
        assert_eq!(on_last_parked_called.load(Ordering::SeqCst), 1);
    }
}
