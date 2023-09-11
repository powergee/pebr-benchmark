mod domain;
mod hazard;
mod retire;
mod thread;

pub use hazard::HazardPointer;

use std::thread_local;

use domain::Domain;
pub use thread::Thread;

pub static DEFAULT_DOMAIN: Domain = Domain::new();

thread_local! {
    pub static DEFAULT_THREAD: Box<Thread> = Box::new(Thread::new(&DEFAULT_DOMAIN));
}
