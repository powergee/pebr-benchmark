#![doc = include_str!("../README.md")]

mod domain;
mod epoch;
mod hazard;
mod queue;
mod tag;
mod thread;

pub use hazard::HazardPointer;
pub use tag::*;

pub(crate) static mut COUNTS_BETWEEN_FLUSH: usize = 64;

#[inline]
pub fn set_counts_between_flush(counts: usize) {
    assert!(
        counts >= 2 && counts % 2 == 0,
        "counts must be even and greater than 1."
    );
    unsafe { COUNTS_BETWEEN_FLUSH = counts };
}

#[inline]
pub fn counts_between_flush() -> usize {
    unsafe { COUNTS_BETWEEN_FLUSH }
}

use std::sync::OnceLock;

use crate::domain::Domain;
pub use crate::thread::Thread;

static DEFAULT_DOMAIN: OnceLock<Domain> = OnceLock::new();

#[inline]
pub fn domain() -> &'static Domain {
    DEFAULT_DOMAIN.get_or_init(Domain::new)
}
