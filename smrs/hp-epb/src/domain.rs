use core::sync::atomic::{AtomicUsize, Ordering};
use std::mem::take;
use std::sync::atomic::fence;

use crossbeam_utils::CachePadded;
use rustc_hash::FxHashSet;

use crate::epoch::{AtomicEpoch, Epoch};
use crate::hazard::ThreadRecords;
use crate::queue::{Bag, DoubleLink, SealedBag};
use crate::thread::Thread;

pub struct Domain {
    pub(crate) threads: CachePadded<ThreadRecords>,
    pub(crate) num_garbages: CachePadded<AtomicUsize>,
    pub(crate) epoch: CachePadded<AtomicEpoch>,
    pub(crate) retireds: DoubleLink,
}

impl Domain {
    pub(crate) fn new() -> Self {
        Self {
            threads: CachePadded::new(ThreadRecords::new()),
            num_garbages: CachePadded::new(AtomicUsize::new(0)),
            epoch: CachePadded::new(AtomicEpoch::new(Epoch::starting())),
            retireds: DoubleLink::new(),
        }
    }

    pub fn collect_guarded_ptrs<'domain>(
        &self,
        reclaimer: &mut Thread<'domain>,
    ) -> FxHashSet<*mut u8> {
        self.threads
            .iter()
            .flat_map(|thread| thread.iter(reclaimer))
            .collect()
    }

    pub fn num_garbages(&self) -> usize {
        self.num_garbages.load(Ordering::Relaxed)
    }

    pub(crate) fn push_bag(&self, bag: &mut Bag) {
        self.num_garbages.fetch_add(bag.len(), Ordering::AcqRel);
        let bag = take(bag);

        fence(Ordering::SeqCst);

        let epoch = self.epoch.load(Ordering::Relaxed);
        self.retireds.push(SealedBag::new(epoch, bag));
    }
}
