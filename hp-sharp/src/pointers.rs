use std::{
    cell::Cell,
    marker::PhantomData,
    mem::{self, swap, transmute, zeroed, MaybeUninit},
    sync::atomic::{compiler_fence, AtomicUsize, Ordering},
};

use membarrier::light_membarrier;

use crate::{
    crcu::Writable, guard::EpochGuard, guard::Invalidate, hazard::HazardPointer, thread::Handle,
    THREAD,
};

/// A result of unsuccessful `compare_exchange`.
pub struct CompareExchangeError<'r, T: 'r> {
    /// The `new` pointer which was given as a parameter of `compare_exchange`.
    pub new: Shared<'r, T>,
    /// The actual pointer value inside the atomic pointer.
    pub actual: Shared<'r, T>,
}

pub struct Atomic<T> {
    link: AtomicUsize,
    _marker: PhantomData<*mut T>,
}

unsafe impl<T> Send for Atomic<T> {}
unsafe impl<T> Sync for Atomic<T> {}

impl<T> Atomic<T> {
    /// Allocates `init` on the heap and returns a new atomic pointer pointing to it.
    #[inline]
    pub fn new(init: T) -> Self {
        let ptr = Box::into_raw(Box::new(init));
        Self {
            link: AtomicUsize::new(ptr as _),
            _marker: PhantomData,
        }
    }

    /// Returns a new null atomic pointer.
    #[inline]
    pub const fn null() -> Self {
        Self {
            link: AtomicUsize::new(0),
            _marker: PhantomData,
        }
    }

    /// Stores a [`Shared`] pointer into the atomic pointer, returning the previous [`Shared`].
    #[inline]
    pub fn swap<G: Writable>(&self, ptr: Shared<T>, order: Ordering, _: &G) -> Shared<T> {
        let prev = self.link.swap(ptr.inner, order);
        Shared::new(prev)
    }

    /// Stores a [`Shared`] pointer into the atomic pointer.
    #[inline]
    pub fn store<G: Writable>(&self, ptr: Shared<T>, order: Ordering, _: &G) {
        self.link.store(ptr.inner, order);
    }

    /// Loads a [`Shared`] from the atomic pointer. This can be called only in a read phase.
    #[inline]
    pub fn load<'r>(&self, order: Ordering, _: &'r EpochGuard) -> Shared<'r, T> {
        let ptr = self.link.load(order);
        Shared::new(ptr)
    }

    /// Stores the pointer `new` into the atomic pointer if the current value is the
    /// same as `current`. The tag is also taken into account, so two pointers to the same object,
    /// but with different tags, will not be considered equal.
    ///
    /// The return value is a result indicating whether the new pointer was written. On success a
    /// [`Shared`] which is taken out from the atomic pointer is returned. On failure a
    /// [`CompareExchangeError`] which contains an actual value from the atomic pointer and
    /// the ownership of `new` pointer which was given as a parameter is returned.
    #[inline]
    pub fn compare_exchange<'p, 'r, G: Writable>(
        &self,
        current: Shared<'p, T>,
        new: Shared<'r, T>,
        success: Ordering,
        failure: Ordering,
        _: &'r G,
    ) -> Result<Shared<T>, CompareExchangeError<'r, T>> {
        let current = current.inner;
        let new = new.inner;

        self.link
            .compare_exchange(current, new, success, failure)
            .map(|actual| Shared::new(actual))
            .map_err(|actual| CompareExchangeError {
                new: Shared::new(new),
                actual: Shared::new(actual),
            })
    }

    /// Bitwise "or" with the current tag.
    ///
    /// Performs a bitwise "or" operation on the current tag and the argument `tag`, and sets the
    /// new tag to the result. Returns the previous pointer.
    #[inline]
    pub fn fetch_or<'r, G: Writable>(
        &self,
        tag: usize,
        order: Ordering,
        _: &'r G,
    ) -> Shared<'r, T> {
        Shared::new(self.link.fetch_or(decompose_data::<T>(tag).1, order))
    }
}

/// A pointer to an shared object.
///
/// This pointer is valid for use only during the lifetime `'r`.
///
/// This is the most basic shared pointer type, which can be loaded directly from [`Atomic`].
/// Also it is worth noting that [`Shield`] can create a [`Shared`] which has a lifetime parameter
/// of the original pointer.
#[derive(Debug)]
pub struct Shared<'r, T: 'r> {
    inner: usize,
    _marker: PhantomData<(&'r (), *const T)>,
}

impl<'r, T> Clone for Shared<'r, T> {
    #[inline]
    fn clone(&self) -> Self {
        Shared {
            inner: self.inner,
            _marker: PhantomData,
        }
    }
}

impl<'r, T> Copy for Shared<'r, T> {}

impl<'r, T> PartialEq for Shared<'r, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<'r, T> Eq for Shared<'r, T> {}

impl<'r, T> Shared<'r, T> {
    #[inline]
    pub(crate) fn new(ptr: usize) -> Self {
        Self {
            inner: ptr,
            _marker: PhantomData,
        }
    }

    /// Returns a new null shared pointer.
    #[inline]
    pub fn null() -> Self {
        Self::new(0)
    }

    /// Returns `true` if the pointer is null.
    #[inline]
    pub fn is_null(&self) -> bool {
        decompose_data::<T>(self.inner).0 as usize == 0
    }

    /// Converts the pointer to a reference.
    ///
    /// Returns `None` if the pointer is null, or else a reference to the object wrapped in `Some`.
    ///
    /// It is possible to directly dereference a [`Shared`] if and only if the current context is
    /// in a read phase which can be started by `read` and `read_loop` method.
    #[inline]
    pub fn as_ref(&self, _: &EpochGuard) -> Option<&'r T> {
        unsafe { decompose_data::<T>(self.inner).0.as_ref() }
    }

    /// Converts the pointer to a reference, without guaranteeing any safety.
    ///
    /// # Safety
    ///
    /// The `self` must be a valid memory location.
    #[inline]
    pub unsafe fn deref_unchecked(&self) -> &T {
        &*decompose_data::<T>(self.inner).0
    }

    /// Returns the tag stored within the pointer.
    #[inline]
    pub fn tag(&self) -> usize {
        decompose_data::<T>(self.inner).1
    }

    /// Returns the same pointer, but the tag bits are cleared.
    #[inline]
    pub fn untagged(&self) -> Self {
        Shared::new(decompose_data::<T>(self.inner).0 as usize)
    }

    /// Returns the same pointer, but tagged with `tag`. `tag` is truncated to be fit into the
    /// unused bits of the pointer to `T`.
    #[inline]
    pub fn with_tag(&self, tag: usize) -> Self {
        Shared::new(data_with_tag::<T>(self.inner, tag))
    }
}

/// A pointer to an shared object, which is protected by a hazard pointer.
pub struct Shield<T: 'static> {
    hazptr: HazardPointer,
    inner: Cell<usize>,
    _marker: PhantomData<T>,
}

unsafe impl<T> Sync for Shield<T> {}

impl<T> Shield<T> {
    #[inline]
    pub fn null(handle: &mut Handle) -> Self {
        Self {
            hazptr: HazardPointer::new(handle),
            inner: Cell::new(0),
            _marker: PhantomData,
        }
    }

    /// Converts the pointer to a reference.
    ///
    /// Returns `None` if the pointer is null, or else a reference to the object wrapped in `Some`.
    #[inline]
    pub fn as_ref<'s>(&'s self) -> Option<&'s T> {
        unsafe { decompose_data::<T>(self.inner.get()).0.as_ref() }
    }

    /// Converts the pointer to a mutable reference.
    ///
    /// Returns `None` if the pointer is null, or else a reference to the object wrapped in `Some`.
    #[inline]
    pub fn as_mut<'s>(&'s self) -> Option<&'s mut T> {
        unsafe { decompose_data::<T>(self.inner.get()).0.as_mut() }
    }

    /// Returns `true` if the defended pointer is null.
    #[inline]
    pub fn is_null(&self) -> bool {
        decompose_data::<T>(self.inner.get()).0 as usize == 0
    }

    /// Returns the tag stored within the shield.
    #[inline]
    pub fn tag(&self) -> usize {
        decompose_data::<T>(self.inner.get()).1
    }

    /// Changes the tag bits to `tag`. `tag` is truncated to be fit into the
    /// unused bits of the pointer to `T`.
    #[inline]
    pub fn set_tag(&self, tag: usize) {
        self.inner.set(data_with_tag::<T>(self.inner.get(), tag));
    }

    /// Releases the inner hazard pointer.
    #[inline]
    pub fn release(&self) {
        self.inner.set(0);
        self.hazptr.reset_protection();
    }
}

impl<T> Default for Shield<T> {
    /// Creates a [`Shield`] with a default [`Thread`].
    #[inline]
    fn default() -> Self {
        THREAD.with(|t| Self::null(&mut t.borrow_mut()))
    }
}

pub trait Pointer<T> {
    /// Returns the machine representation of the pointer, including tag bits.
    fn as_raw(&self) -> usize;
}

impl<'r, T> Pointer<T> for Shared<'r, T> {
    #[inline]
    fn as_raw(&self) -> usize {
        self.inner
    }
}

impl<T> Pointer<T> for Shield<T> {
    #[inline]
    fn as_raw(&self) -> usize {
        self.inner.get()
    }
}

/// A trait for `Shield` which can protect `Shared`.
pub trait Defender {
    /// A set of `Shared` pointers which is protected by an epoch.
    type Read<'r>: Clone + Copy;

    /// Returns a default `Defender` with nulls for [`Shield`]s and defaults for other types.
    fn empty(handle: &mut Handle) -> Self;

    /// Stores the given `Read` pointers in hazard slots without any validations.
    ///
    /// # Safety
    ///
    /// Just storing a pointer in a hazard slot doesn't guarantee that the pointer is
    /// truly protected, as the memory block may already be reclaimed. We must validate whether
    /// the memory block is reclaimed or not, by reloading the atomic pointer or checking the
    /// local CRCU epoch.
    unsafe fn defend_unchecked(&self, read: &Self::Read<'_>);

    /// Loads currently protected pointers and checks whether any of them are invalidated.
    /// If not, creates a new `Read` and returns it.
    unsafe fn as_read<'r>(&self) -> Option<Self::Read<'r>>;

    /// Resets all hazard slots, allowing the previous memory block to be reclaimed.
    fn release(&self);

    /// Starts a crashable critical section where we cannot perform operations with side-effects,
    /// such as system calls, non-atomic write on a global variable, etc.
    ///
    /// After finishing the section, it defends the returned `Read` pointers, so that they can be
    /// dereferenced outside of the phase.
    ///
    /// # Safety
    ///
    /// In a section body, only *rollback-safe* operations are allowed. For example, non-atomic
    /// writes on a global variable and system-calls(File I/O and etc.) are dangerous, as they
    /// may cause an unexpected inconsistency on the whole system after a crash.
    unsafe fn pin<F>(&mut self, handle: &mut Handle, body: F)
    where
        F: for<'r> Fn(&'r mut EpochGuard) -> Self::Read<'r>,
    {
        handle.crcu_handle.pin(|guard| {
            // Execute the body of this read phase.
            let mut guard = EpochGuard::new(guard, handle, None);
            let result = body(&mut guard);
            compiler_fence(Ordering::SeqCst);

            // Store pointers in hazard slots and issue a light fence.
            self.defend_unchecked(&result);
            light_membarrier();

            // If we successfully defended pointers without an intermediate crash,
            // it has the same meaning with a well-known HP validation:
            // we can safely assume that the pointers are not reclaimed yet.
        })
    }

    /// Starts a crashable critical section where we cannot perform operations with side-effects,
    /// such as system calls, non-atomic write on a global variable, etc.
    ///
    /// This is similar to `pin`, as it manages CRCU critical section. However, this `pin_loop`
    /// prevents a starvation in crash-intensive workload by saving intermediate results on a
    /// backup `Defender`.
    ///
    /// After finishing the section, it defends the final `Read` pointers, so that they can be
    /// dereferenced outside of the phase.
    ///
    /// # Safety
    ///
    /// In a section body, only *rollback-safe* operations are allowed. For example, non-atomic
    /// writes on a global variable and system-calls(File I/O and etc.) are dangerous, as they
    /// may cause an unexpected inconsistency on the whole system after a crash.
    unsafe fn pin_loop<F1, F2>(
        &mut self,
        backup: &mut Self,
        handle: &mut Handle,
        init_result: F1,
        step_forward: F2,
    ) where
        F1: for<'r> Fn(&'r mut EpochGuard) -> Self::Read<'r>,
        F2: for<'r> Fn(&mut Self::Read<'r>, &'r mut EpochGuard) -> ReadStatus,
        Self: Sized,
    {
        const ITER_BETWEEN_CHECKPOINTS: usize = 512;

        // `backup_idx` indicates where we have stored the latest backup to `backup_def`.
        // 0 = `defs[0]`, 1 = `defs[1]`, otherwise = no backup
        // We use an atomic type instead of regular one, to perform writes atomically,
        // so that stored data is consistent even if a crash occured during a write.
        let backup_idx = AtomicUsize::new(2);
        {
            let defs = [&mut *self, backup];

            handle.crcu_handle.pin(|guard| {
                // Load the saved intermediate result, if one exists.
                let mut guard = EpochGuard::new(guard, handle, Some(&backup_idx));
                let mut result = defs
                    .get(backup_idx.load(Ordering::Relaxed))
                    .and_then(|def| def.as_read())
                    .unwrap_or_else(|| init_result(transmute(&mut guard)));

                for iter in 0.. {
                    // Execute a single step.
                    let step_result = step_forward(&mut result, transmute(&mut guard));

                    let finished = step_result == ReadStatus::Finished;
                    // TODO(@jeonghyeon): Apply an adaptive checkpointing.
                    let should_checkpoint =
                        step_result == ReadStatus::Continue && iter % ITER_BETWEEN_CHECKPOINTS == 0;

                    if finished || should_checkpoint {
                        if iter % ITER_BETWEEN_CHECKPOINTS == 0 {
                            // Select an available defender to protect a backup.
                            let (curr_def, next_def, next_idx) = {
                                let backup_idx = backup_idx.load(Ordering::Relaxed);
                                (
                                    &defs[backup_idx % 2],
                                    &defs[(backup_idx + 1) % 2],
                                    (backup_idx + 1) % 2,
                                )
                            };

                            // Store pointers in hazard slots and issue a light fence.
                            unsafe { next_def.defend_unchecked(&result) };
                            membarrier::light_membarrier();

                            // Success! We are not ejected so the protection is valid!
                            // Finalize backup process by storing a new backup index to `backup_idx`
                            backup_idx.store(next_idx, Ordering::Relaxed);
                            curr_def.release();
                        }
                    }

                    // The task is finished! Break the loop and return the result.
                    if finished {
                        break;
                    }
                }
            });
        }

        // We want that `self` contains the final result.
        // If the latest backup is `backup`, than swap `self` and `backup`.
        let backup_idx = backup_idx.load(Ordering::Relaxed);
        assert!(backup_idx < 2);
        if backup_idx == 1 {
            swap(self, backup);
        }
    }
}

/// An empty `Defender`.
impl Defender for () {
    type Read<'r> = ();

    #[inline]
    fn empty(_: &mut Handle) -> Self {
        ()
    }

    #[inline]
    unsafe fn defend_unchecked(&self, _: &Self::Read<'_>) {}

    #[inline]
    unsafe fn as_read<'r>(&self) -> Option<Self::Read<'r>> {
        Some(())
    }

    #[inline]
    fn release(&self) {}
}

/// A unit `Defender` with a single `Shield`.
impl<T: Invalidate> Defender for Shield<T> {
    type Read<'r> = Shared<'r, T>;

    #[inline]
    fn empty(handle: &mut Handle) -> Self {
        Shield::null(handle)
    }

    #[inline]
    unsafe fn defend_unchecked(&self, read: &Self::Read<'_>) {
        let raw = read.untagged().as_raw();
        self.hazptr.protect_raw(raw as *const T as *mut T);
        self.inner.set(raw);
    }

    #[inline]
    unsafe fn as_read<'r>(&self) -> Option<Self::Read<'r>> {
        let read = Shared::new(self.inner.get());
        if let Some(value) = self.as_ref() {
            if value.is_invalidated() {
                return None;
            }
        }
        Some(read)
    }

    #[inline]
    fn release(&self) {
        Shield::release(self)
    }
}

macro_rules! impl_defender_for_array {(
    $($N:literal)*
) => (
    $(
        impl<T: Invalidate> Defender for [Shield<T>; $N] {
            type Read<'r> = [Shared<'r, T>; $N];

            #[inline]
            fn empty(handle: &mut Handle) -> Self {
                let mut result: [MaybeUninit<Shield<T>>; $N] = unsafe { zeroed() };
                for shield in result.iter_mut() {
                    shield.write(Shield::null(handle));
                }
                unsafe { transmute(result) }
            }

            #[inline]
            unsafe fn defend_unchecked(&self, read: &Self::Read<'_>) {
                for (shield, shared) in self.iter().zip(read) {
                    shield.defend_unchecked(shared);
                }
            }

            #[inline]
            unsafe fn as_read<'r>(&self) -> Option<Self::Read<'r>> {
                let mut result: [MaybeUninit<Shared<'r, T>>; $N] = zeroed();
                for (shield, shared) in self.iter().zip(result.iter_mut()) {
                    match shield.as_read() {
                        Some(read) => shared.write(read),
                        None => return None,
                    };
                }
                Some(transmute(result))
            }

            #[inline]
            fn release(&self) {
                for shield in self {
                    shield.release();
                }
            }
        }
    )*
)}

impl_defender_for_array! {
    00
    01 02 03 04 05 06 07 08
    09 10 11 12 13 14 15 16
    17 18 19 20 21 22 23 24
    25 26 27 28 29 30 31 32
}

/// A result of a single step of an iterative critical section.
#[derive(PartialEq, Eq)]
pub enum ReadStatus {
    /// The entire task is finished.
    Finished,
    /// We need to take one or more steps.
    Continue,
}

/// A result of a non-crashable section.
#[derive(PartialEq, Eq)]
pub enum WriteResult {
    /// The section is normally finished. Resume the task.
    Finished,
    /// Give up the current epoch and restart the whole critical section.
    RepinEpoch,
}

/// Panics if the pointer is not properly unaligned.
#[inline]
pub fn ensure_aligned<T>(raw: *const T) {
    assert_eq!(raw as usize & low_bits::<T>(), 0, "unaligned pointer");
}

/// Returns a bitmask containing the unused least significant bits of an aligned pointer to `T`.
#[inline]
pub fn low_bits<T>() -> usize {
    (1 << mem::align_of::<T>().trailing_zeros()) - 1
}

/// Given a tagged pointer `data`, returns the same pointer, but tagged with `tag`.
///
/// `tag` is truncated to fit into the unused bits of the pointer to `T`.
#[inline]
pub fn data_with_tag<T>(data: usize, tag: usize) -> usize {
    (data & !low_bits::<T>()) | (tag & low_bits::<T>())
}

/// Decomposes a tagged pointer `data` into the pointer and the tag.
#[inline]
pub fn decompose_data<T>(data: usize) -> (*mut T, usize) {
    let raw = (data & !low_bits::<T>()) as *mut T;
    let tag = data & low_bits::<T>();
    (raw, tag)
}
