use core::ptr;
use core::sync::atomic::{AtomicPtr, Ordering};
use std::sync::atomic::{compiler_fence, fence};

use rustc_hash::FxHashSet;

use crate::domain::Domain;
use crate::epoch::Epoch;
use crate::hazard::ThreadRecord;
use crate::queue::{Bag, Deferred};

pub struct Thread<'domain> {
    pub(crate) domain: &'domain Domain,
    pub(crate) hazards: &'domain ThreadRecord,
    /// available slots of hazard array
    pub(crate) available_indices: Vec<usize>,
    #[allow(unused)]
    pub(crate) failed_advances: usize,
    pub(crate) retired: Bag,
}

impl<'domain> Thread<'domain> {
    pub fn new(domain: &'domain Domain) -> Self {
        let (thread, available_indices) = domain.threads.acquire();
        Self {
            domain,
            hazards: thread,
            available_indices,
            failed_advances: 0,
            retired: Bag::new(),
        }
    }
}

// stuff related to reclamation
impl<'domain> Thread<'domain> {
    #[allow(unused)]
    const FORCE_ADVANCE_THRESHOLD: usize = 2;

    // NOTE: T: Send not required because we reclaim only locally.
    #[inline]
    pub unsafe fn retire<T>(&mut self, ptr: *mut T) {
        self.push_def(Deferred::new(ptr as _, free::<T>));
    }

    #[inline]
    fn push_def(&mut self, def: Deferred) {
        if let Err(d) = self.retired.try_push(def) {
            self.domain.push_bag(&mut self.retired);
            self.retired.try_push(d).unwrap();

            let epoch = match self.try_advance() {
                Ok(epoch) | Err(epoch) => epoch,
            };
            self.collect(epoch);

            // if self.failed_advances >= Self::FORCE_ADVANCE_THRESHOLD {
            //     self.failed_advances = 0;
            //     self.collect(self.advance());
            // } else if let Ok(epoch) = self.try_advance() {
            //     self.failed_advances = 0;
            //     self.collect(epoch);
            // } else {
            //     self.failed_advances += 1;
            // }
        }
    }

    #[inline]
    fn collect(&mut self, current: Epoch) {
        let mut guarded_ptrs = None;
        for _ in 0..8 {
            if let Some(bag) = self.domain.retireds.pop_if(|bag| bag.is_expired(current)) {
                let guarded_ptrs =
                    guarded_ptrs.get_or_insert_with(|| self.domain.collect_guarded_ptrs(self));
                self.process_expired(guarded_ptrs, bag.into_inner());
            } else {
                break;
            }
        }
    }

    #[inline]
    fn process_expired(&mut self, guarded_ptrs: &FxHashSet<*mut u8>, bag: Bag) {
        let mut freed = 0;
        for def in bag.into_iter() {
            if guarded_ptrs.contains(&def.data()) {
                self.push_def(def);
            } else {
                unsafe { def.execute() };
                freed += 1;
            }
        }
        self.domain.num_garbages.fetch_sub(freed, Ordering::AcqRel);
    }
}

// stuff related to hazards
impl<'domain> Thread<'domain> {
    /// acquire hazard slot
    pub(crate) fn acquire(&mut self) -> usize {
        if let Some(idx) = self.available_indices.pop() {
            idx
        } else {
            self.grow_array();
            self.acquire()
        }
    }

    fn grow_array(&mut self) {
        let array_ptr = self.hazards.hazptrs.load(Ordering::Relaxed);
        let array = unsafe { &*array_ptr };
        let size = array.len();
        let new_size = size * 2;
        let mut new_array = Box::new(Vec::with_capacity(new_size));
        for i in 0..size {
            new_array.push(AtomicPtr::new(array[i].load(Ordering::Relaxed)));
        }
        for _ in size..new_size {
            new_array.push(AtomicPtr::new(ptr::null_mut()));
        }
        self.hazards
            .hazptrs
            .store(Box::into_raw(new_array), Ordering::Release);
        unsafe { self.retire(array_ptr) };
        self.available_indices.extend(size..new_size)
    }

    /// release hazard slot
    pub(crate) fn release(&mut self, idx: usize) {
        self.available_indices.push(idx);
    }
}

// stuff related to barriers
impl<'domain> Thread<'domain> {
    #[inline]
    pub fn light_fence(&self) {
        compiler_fence(Ordering::SeqCst);
        let global_epoch = self.domain.epoch.load(Ordering::Relaxed);
        let local_epoch = self.hazards.epoch.load(Ordering::Relaxed);
        if !local_epoch.is_pinned() || local_epoch.value() < global_epoch.value() {
            self.repin(global_epoch.pinned());
        }
    }

    #[inline]
    #[cold]
    fn repin(&self, new: Epoch) {
        self.hazards.epoch.store(new, Ordering::Relaxed);
        fence(Ordering::SeqCst);
    }

    /// Try advancing the global epoch and returns the current epoch value.
    #[inline]
    pub(crate) fn try_advance(&self) -> Result<Epoch, Epoch> {
        let global_epoch = self.domain.epoch.load(Ordering::Relaxed);
        self.hazards
            .epoch
            .store(global_epoch.pinned(), Ordering::Relaxed);
        fence(Ordering::SeqCst);

        for thread in self.domain.threads.iter() {
            let thread_epoch = thread.epoch.load(Ordering::Relaxed);

            // Someone has advanced the global epoch already.
            if thread_epoch.value() > global_epoch.value() {
                return Ok(thread_epoch);
            }

            // If the participant was pinned in a different epoch, we cannot advance the
            // global epoch just yet.
            if thread_epoch.is_pinned() && thread_epoch.unpinned().value() < global_epoch.value() {
                return Err(global_epoch);
            }
        }
        fence(Ordering::Acquire);

        // All pinned participants were pinned in the current global epoch.
        // Now let's advance the global epoch...
        //
        // Note that advancing here may fail if other thread already have advanced the epoch.
        let new_epoch = global_epoch.successor();
        let _ = self.domain.epoch.compare_exchange(
            global_epoch,
            new_epoch,
            Ordering::Release,
            Ordering::Relaxed,
        );
        Ok(new_epoch)
    }

    /// Advance the global epoch (forcefully) and returns the current epoch value.
    #[inline]
    #[allow(unused)]
    pub(crate) fn advance(&self) -> Epoch {
        match self.try_advance() {
            Ok(global_epoch) => return global_epoch,
            Err(global_epoch) => {
                membarrier::heavy();
                for thread in self.domain.threads.iter() {
                    let thread_epoch = thread.epoch.load(Ordering::Relaxed);
                    if thread_epoch.value() == global_epoch.value() {
                        thread.epoch.store(Epoch::starting(), Ordering::Relaxed);
                    }
                }

                let new_epoch = global_epoch.successor();
                let _ = self.domain.epoch.compare_exchange(
                    global_epoch,
                    new_epoch,
                    Ordering::Release,
                    Ordering::Relaxed,
                );
                return global_epoch;
            }
        }
    }
}

impl<'domain> Drop for Thread<'domain> {
    fn drop(&mut self) {
        self.domain.push_bag(&mut self.retired);
        self.available_indices.clear();
        self.domain.threads.release(self.hazards);
    }
}

pub(crate) unsafe fn free<T>(ptr: *mut u8) {
    let ptr = ptr as *mut T;
    drop(Box::from_raw(ptr));
}
