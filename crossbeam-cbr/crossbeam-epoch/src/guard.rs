use core::fmt;
use core::mem;
use core::mem::MaybeUninit;
use core::ptr::drop_in_place;
use core::ptr::read_volatile;
use core::ptr::write_volatile;
use core::sync::atomic::compiler_fence;
use core::sync::atomic::fence;
use core::sync::atomic::AtomicUsize;
use core::sync::atomic::Ordering;

use nix::sys::signal::pthread_sigmask;
use nix::sys::signal::SigmaskHow;
use nix::sys::signalfd::SigSet;

use crate::atomic::Shared;
use crate::collector::Collector;
use crate::deferred::Deferred;
use crate::garbage::Garbage;
use crate::hazard::Shield;
use crate::internal::Local;
use crate::rc::Localizable;
use crate::recovery;

/// A guard that keeps the current thread pinned.
///
/// # Pinning
///
/// The current thread is pinned by calling [`pin`], which returns a new guard:
///
/// ```
/// use crossbeam_cbr_epoch as epoch;
///
/// // It is often convenient to prefix a call to `pin` with a `&` in order to create a reference.
/// // This is not really necessary, but makes passing references to the guard a bit easier.
/// let guard = &epoch::pin();
/// ```
///
/// When a guard gets dropped, the current thread is automatically unpinned.
///
/// # Pointers on the stack
///
/// Having a guard allows us to create pointers on the stack to heap-allocated objects.
/// For example:
///
/// ```
/// use crossbeam_cbr_epoch::{self as epoch, Atomic, Owned};
/// use std::sync::atomic::Ordering::SeqCst;
///
/// // Create a heap-allocated number.
/// let a = Atomic::new(777);
///
/// // Pin the current thread.
/// let guard = &epoch::pin();
///
/// // Load the heap-allocated object and create pointer `p` on the stack.
/// let p = a.load(SeqCst, guard);
///
/// // Dereference the pointer and print the value:
/// if let Some(num) = unsafe { p.as_ref() } {
///     println!("The number is {}.", num);
/// }
/// ```
///
/// # Multiple guards
///
/// Pinning is reentrant and it is perfectly legal to create multiple guards. In that case, the
/// thread will actually be pinned only when the first guard is created and unpinned when the last
/// one is dropped:
///
/// ```
/// use crossbeam_cbr_epoch as epoch;
///
/// let guard1 = epoch::pin();
/// let guard2 = epoch::pin();
/// assert!(epoch::is_pinned());
/// drop(guard1);
/// assert!(epoch::is_pinned());
/// drop(guard2);
/// assert!(!epoch::is_pinned());
/// ```
///
/// [`pin`]: fn.pin.html
pub struct EpochGuard {
    pub(crate) local: *const Local,
}

impl EpochGuard {
    #[inline]
    unsafe fn defer_garbage(&self, garbage: Garbage, internal: bool) {
        if let Some(local) = self.local.as_ref() {
            local.defer(garbage, self, internal);
        } else {
            garbage.dispose();
        }
    }

    /// Stores a function so that it can be executed at some point after all currently pinned
    /// threads get unpinned.
    ///
    /// This method first stores `f` into the thread-local (or handle-local) cache. If this cache
    /// becomes full, some functions are moved into the global cache. At the same time, some
    /// functions from both local and global caches may get executed in order to incrementally
    /// clean up the caches as they fill up.
    ///
    /// There is no guarantee when exactly `f` will be executed. The only guarantee is that it
    /// won't be executed until all currently pinned threads get unpinned. In theory, `f` might
    /// never run, but the epoch-based garbage collection will make an effort to execute it
    /// reasonably soon.
    ///
    /// If this method is called from an [`unprotected`] guard, the function will simply be
    /// executed immediately.
    ///
    /// [`unprotected`]: fn.unprotected.html
    #[inline]
    pub fn defer<F, R>(&self, f: F)
    where
        F: FnOnce() -> R,
        F: Send + 'static,
    {
        unsafe {
            self.defer_unchecked(f);
        }
    }

    /// Stores a function so that it can be executed at some point after all currently pinned
    /// threads get unpinned.
    ///
    /// This method first stores `f` into the thread-local (or handle-local) cache. If this cache
    /// becomes full, some functions are moved into the global cache. At the same time, some
    /// functions from both local and global caches may get executed in order to incrementally
    /// clean up the caches as they fill up.
    ///
    /// There is no guarantee when exactly `f` will be executed. The only guarantee is that it
    /// won't be executed until all currently pinned threads get unpinned. In theory, `f` might
    /// never run, but the epoch-based garbage collection will make an effort to execute it
    /// reasonably soon.
    ///
    /// If this method is called from an [`unprotected`] guard, the function will simply be
    /// executed immediately.
    ///
    /// # Safety
    ///
    /// The given function must not hold reference onto the stack. It is highly recommended that
    /// the passed function is **always** marked with `move` in order to prevent accidental
    /// borrows.
    ///
    /// ```
    /// use crossbeam_cbr_epoch as epoch;
    ///
    /// let guard = &epoch::pin();
    /// let message = "Hello!";
    /// unsafe {
    ///     // ALWAYS use `move` when sending a closure into `defer_unchecked`.
    ///     guard.defer_unchecked(move || {
    ///         println!("{}", message);
    ///     });
    /// }
    /// ```
    ///
    /// Apart from that, keep in mind that another thread may execute `f`, so anything accessed by
    /// the closure must be `Send`.
    ///
    /// We intentionally didn't require `F: Send`, because Rust's type systems usually cannot prove
    /// `F: Send` for typical use cases. For example, consider the following code snippet, which
    /// exemplifies the typical use case of deferring the deallocation of a shared reference:
    ///
    /// ```ignore
    /// let shared = Owned::new(7i32).into_shared(guard);
    /// guard.defer_unchecked(move || shared.into_owned()); // `Shared` is not `Send`!
    /// ```
    ///
    /// While `Shared` is not `Send`, it's safe for another thread to call the deferred function,
    /// because it's called only after the grace period and `shared` is no longer shared with other
    /// threads. But we don't expect type systems to prove this.
    ///
    /// # Examples
    ///
    /// When a heap-allocated object in a data structure becomes unreachable, it has to be
    /// deallocated. However, the current thread and other threads may be still holding references
    /// on the stack to that same object. Therefore it cannot be deallocated before those references
    /// get dropped. This method can defer deallocation until all those threads get unpinned and
    /// consequently drop all their references on the stack.
    ///
    /// ```
    /// use crossbeam_cbr_epoch::{self as epoch, Atomic, Owned};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// let a = Atomic::new("foo");
    ///
    /// // Now suppose that `a` is shared among multiple threads and concurrently
    /// // accessed and modified...
    ///
    /// // Pin the current thread.
    /// let guard = &epoch::pin();
    ///
    /// // Steal the object currently stored in `a` and swap it with another one.
    /// let p = a.swap(Owned::new("bar").into_shared(guard), SeqCst, guard);
    ///
    /// if !p.is_null() {
    ///     // The object `p` is pointing to is now unreachable.
    ///     // Defer its deallocation until all currently pinned threads get unpinned.
    ///     unsafe {
    ///         // ALWAYS use `move` when sending a closure into `defer_unchecked`.
    ///         guard.defer_unchecked(move || {
    ///             println!("{} is now being deallocated.", p.deref());
    ///             // Now we have unique access to the object pointed to by `p` and can turn it
    ///             // into an `Owned`. Dropping the `Owned` will deallocate the object.
    ///             drop(p.into_owned());
    ///         });
    ///     }
    /// }
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    pub unsafe fn defer_unchecked<F, R>(&self, f: F)
    where
        F: FnOnce() -> R,
    {
        self.defer_garbage(
            Garbage::Deferred {
                inner: Deferred::new(move || drop(f())),
            },
            false,
        );
    }

    /// Stores a destructor for an object so that it can be deallocated and dropped at some point
    /// after all currently pinned threads get unpinned.
    ///
    /// This method first stores the destructor into the thread-local (or handle-local) cache. If
    /// this cache becomes full, some destructors are moved into the global cache. At the same
    /// time, some destructors from both local and global caches may get executed in order to
    /// incrementally clean up the caches as they fill up.
    ///
    /// There is no guarantee when exactly the destructor will be executed. The only guarantee is
    /// that it won't be executed until all currently pinned threads get unpinned. In theory, the
    /// destructor might never run, but the epoch-based garbage collection will make an effort to
    /// execute it reasonably soon.
    ///
    /// If this method is called from an [`unprotected`] guard, the destructor will simply be
    /// executed immediately.
    ///
    /// # Safety
    ///
    /// The object must not be reachable by other threads anymore, otherwise it might be still in
    /// use when the destructor runs.
    ///
    /// Apart from that, keep in mind that another thread may execute the destructor, so the object
    /// must be sendable to other threads.
    ///
    /// We intentionally didn't require `T: Send`, because Rust's type systems usually cannot prove
    /// `T: Send` for typical use cases. For example, consider the following code snippet, which
    /// exemplifies the typical use case of deferring the deallocation of a shared reference:
    ///
    /// ```ignore
    /// let shared = Owned::new(7i32).into_shared(guard);
    /// guard.defer_destroy(shared); // `Shared` is not `Send`!
    /// ```
    ///
    /// While `Shared` is not `Send`, it's safe for another thread to call the destructor, because
    /// it's called only after the grace period and `shared` is no longer shared with other
    /// threads. But we don't expect type systems to prove this.
    ///
    /// # Examples
    ///
    /// When a heap-allocated object in a data structure becomes unreachable, it has to be
    /// deallocated. However, the current thread and other threads may be still holding references
    /// on the stack to that same object. Therefore it cannot be deallocated before those references
    /// get dropped. This method can defer deallocation until all those threads get unpinned and
    /// consequently drop all their references on the stack.
    ///
    /// ```
    /// use crossbeam_cbr_epoch::{self as epoch, Atomic, Owned};
    /// use std::sync::atomic::Ordering::SeqCst;
    ///
    /// let a = Atomic::new("foo");
    ///
    /// // Now suppose that `a` is shared among multiple threads and concurrently
    /// // accessed and modified...
    ///
    /// // Pin the current thread.
    /// let guard = &epoch::pin();
    ///
    /// // Steal the object currently stored in `a` and swap it with another one.
    /// let p = a.swap(Owned::new("bar").into_shared(guard), SeqCst, guard);
    ///
    /// if !p.is_null() {
    ///     // The object `p` is pointing to is now unreachable.
    ///     // Defer its deallocation until all currently pinned threads get unpinned.
    ///     unsafe {
    ///         guard.defer_destroy(p);
    ///     }
    /// }
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    #[inline]
    pub unsafe fn defer_destroy<T>(&self, ptr: Shared<T>) {
        unsafe fn dtor<T>(data: usize) {
            drop(Shared::from(data as *const T).into_owned());
        }

        self.defer_garbage(
            Garbage::Destroy {
                data: ptr.as_raw() as usize,
                dtor: dtor::<T>,
            },
            false,
        );
    }

    #[inline]
    pub(crate) unsafe fn defer_destroy_internal<T>(&self, ptr: Shared<T>) {
        unsafe fn dtor<T>(data: usize) {
            drop(Shared::from(data as *const T).into_owned());
        }

        self.defer_garbage(
            Garbage::Destroy {
                data: ptr.as_raw() as usize,
                dtor: dtor::<T>,
            },
            true,
        );
    }

    /// Clears up the thread-local cache of deferred functions by executing them or moving into the
    /// global cache.
    ///
    /// Call this method after deferring execution of a function if you want to get it executed as
    /// soon as possible. Flushing will make sure it is residing in in the global cache, so that
    /// any thread has a chance of taking the function and executing it.
    ///
    /// If this method is called from an [`unprotected`] guard, it is a no-op (nothing happens).
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_cbr_epoch as epoch;
    ///
    /// let guard = &epoch::pin();
    /// unsafe {
    ///     guard.defer(move || {
    ///         println!("This better be printed as soon as possible!");
    ///     });
    /// }
    /// guard.flush();
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    pub fn flush(&self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.flush(self);
        }
    }

    /// Unpins and then immediately re-pins the thread.
    ///
    /// This method is useful when you don't want delay the advancement of the global epoch by
    /// holding an old epoch. For safety, you should not maintain any guard-based reference across
    /// the call (the latter is enforced by `&mut self`). The thread will only be repinned if this
    /// is the only active guard for the current thread.
    ///
    /// If this method is called from an [`unprotected`] guard, then the call will be just no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_cbr_epoch::{self as epoch, Atomic};
    /// use std::sync::atomic::Ordering::SeqCst;
    /// use std::thread;
    /// use std::time::Duration;
    ///
    /// let a = Atomic::new(777);
    /// let mut guard = epoch::pin();
    /// {
    ///     let p = a.load(SeqCst, &guard);
    ///     assert_eq!(unsafe { p.as_ref() }, Some(&777));
    /// }
    /// guard.repin();
    /// {
    ///     let p = a.load(SeqCst, &guard);
    ///     assert_eq!(unsafe { p.as_ref() }, Some(&777));
    /// }
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    pub fn repin(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.repin();
        }
    }

    /// Temporarily unpins the thread, executes the given function and then re-pins the thread.
    ///
    /// This method is useful when you need to perform a long-running operation (e.g. sleeping)
    /// and don't need to maintain any guard-based reference across the call (the latter is enforced
    /// by `&mut self`). The thread will only be unpinned if this is the only active guard for the
    /// current thread.
    ///
    /// If this method is called from an [`unprotected`] guard, then the passed function is called
    /// directly without unpinning the thread.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_cbr_epoch::{self as epoch, Atomic};
    /// use std::sync::atomic::Ordering::SeqCst;
    /// use std::thread;
    /// use std::time::Duration;
    ///
    /// let a = Atomic::new(777);
    /// let mut guard = epoch::pin();
    /// {
    ///     let p = a.load(SeqCst, &guard);
    ///     assert_eq!(unsafe { p.as_ref() }, Some(&777));
    /// }
    /// guard.repin_after(|| thread::sleep(Duration::from_millis(50)));
    /// {
    ///     let p = a.load(SeqCst, &guard);
    ///     assert_eq!(unsafe { p.as_ref() }, Some(&777));
    /// }
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    pub fn repin_after<F, R>(&mut self, f: F) -> R
    where
        F: FnOnce() -> R,
    {
        if let Some(local) = unsafe { self.local.as_ref() } {
            // We need to acquire a handle here to ensure the Local doesn't
            // disappear from under us.
            local.acquire_handle();
            local.unpin();
        }

        // Ensure the Guard is re-pinned even if the function panics
        defer! {
            if let Some(local) = unsafe { self.local.as_ref() } {
                mem::forget(local.pin());
                local.release_handle();
            }
        }

        f()
    }

    /// Returns the `Collector` associated with this guard.
    ///
    /// This method is useful when you need to ensure that all guards used with
    /// a data structure come from the same collector.
    ///
    /// If this method is called from an [`unprotected`] guard, then `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use crossbeam_cbr_epoch as epoch;
    ///
    /// let mut guard1 = epoch::pin();
    /// let mut guard2 = epoch::pin();
    /// assert!(guard1.collector() == guard2.collector());
    /// ```
    ///
    /// [`unprotected`]: fn.unprotected.html
    pub fn collector(&self) -> Option<&Collector> {
        unsafe { self.local.as_ref().map(|local| local.collector()) }
    }

    unsafe fn is_ejected(&self) -> bool {
        if let Some(local) = self.local.as_ref() {
            return local.get_epoch(self).is_err();
        }
        false
    }

    #[inline(never)]
    pub fn read<'r, F, P>(&mut self, f: F) -> P::Localized
    where
        F: Fn(&'r mut ReadGuard) -> P,
        P: Localizable<'r>,
    {
        // TODO(@jeonghyeon): Those lots of `compiler_fence`s are really necessary?

        // Make a checkpoint with `sigsetjmp` for recovering in read phase.
        compiler_fence(Ordering::SeqCst);
        let buf = recovery::jmp_buf();
        if unsafe { setjmp::sigsetjmp(buf, 0) } == 1 {
            fence(Ordering::SeqCst);

            // Repin the current epoch.
            self.repin();

            // Unblock the signal before restarting the phase.
            let mut oldset = SigSet::empty();
            oldset.add(unsafe { recovery::ejection_signal() });
            if pthread_sigmask(SigmaskHow::SIG_UNBLOCK, Some(&oldset), None).is_err() {
                panic!("Failed to unblock signal");
            }
        }
        compiler_fence(Ordering::SeqCst);

        let mut guard = ReadGuard::new(self);

        // Get ready to open the phase by setting atomic indicators.
        assert!(
            !recovery::is_restartable(),
            "restartable value should be false before starting read phase"
        );
        recovery::initialize_before_read();
        compiler_fence(Ordering::SeqCst);

        // Execute the body of this read phase.
        //
        // Here, `transmute` is needed to bypass a lifetime parameter error.
        //
        // Although `Localizable` is depends on the lifetime of the `ReadGuard`,
        // the `Localizable<'_>::Localized` is independent on it.
        // However, Rust compiler cannot understand this semantics, so we need to
        // lengthen the lifetime of the `guard` to trick the compiler that
        // returned `localized` has sufficient lifetime.
        let result = f(unsafe { mem::transmute(&mut guard) });
        compiler_fence(Ordering::SeqCst);

        // Finaly, close this read phase by unsetting the `RESTARTABLE`.
        recovery::set_restartable(false);

        // Protecting must be conducted in a crash-free section.
        // Otherwise it may forget to drop acquired hazard slot on crashing.
        let localized = result.protect_with(self);
        compiler_fence(Ordering::SeqCst);
        if unsafe { self.is_ejected() } {
            drop(localized);
            unsafe { recovery::perform_longjmp() };
        }
        localized
    }

    #[inline(never)]
    pub fn read_loop<'r, F1, F2, P>(&mut self, init_result: F1, step_forward: F2) -> P::Localized
    where
        F1: Fn(&'r mut ReadGuard) -> P,
        F2: Fn(&mut P, &'r mut ReadGuard) -> ReadStatus,
        P: Localizable<'r> + Clone + Copy,
    {
        const ITER_BETWEEN_CHECKPOINTS: usize = 4096;

        // TODO(@jeonghyeon): Those lots of `compiler_fence`s are really necessary?

        // Pre-allocate a raw backup storage on a heap.
        // TODO(@jeonghyeon): Answer those questions.
        // * Why not on a stack? -> it may optimize to a register
        // * Why a raw pointer, instead of just a `Box`? -> to use volatile
        let backup_result = Box::into_raw(Box::new(unsafe { mem::zeroed::<P>() }));
        let backup_exist = Box::into_raw(Box::new(false));
        let backup_shield = Box::into_raw(Box::new(MaybeUninit::new(unsafe {
            mem::zeroed::<P::Localized>()
        })));

        // Make a checkpoint with `sigsetjmp` for recovering in read phase.
        compiler_fence(Ordering::SeqCst);
        let buf = recovery::jmp_buf();
        if unsafe { setjmp::sigsetjmp(buf, 0) } == 1 {
            fence(Ordering::SeqCst);

            // Repin the current epoch.
            self.repin();

            // Unblock the signal before restarting the phase.
            let mut oldset = SigSet::empty();
            oldset.add(unsafe { recovery::ejection_signal() });
            if pthread_sigmask(SigmaskHow::SIG_UNBLOCK, Some(&oldset), None).is_err() {
                panic!("Failed to unblock signal");
            }
        }
        compiler_fence(Ordering::SeqCst);

        let mut guard = ReadGuard::new(self);

        // Load the saved intermediate result, if one exists.
        let mut result = if unsafe { *backup_exist } {
            unsafe { read_volatile(backup_result.cast_const()) }
        } else {
            init_result(unsafe { mem::transmute(&mut guard) })
        };

        // Get ready to open the phase by setting atomic indicators.
        assert!(
            !recovery::is_restartable(),
            "restartable value should be false before starting read phase"
        );
        recovery::initialize_before_read();
        compiler_fence(Ordering::SeqCst);

        for iter in 0.. {
            match step_forward(&mut result, unsafe { mem::transmute(&mut guard) }) {
                ReadStatus::Finished => break,
                ReadStatus::Continue => {
                    // TODO(@jeonghyeon): Apply an adaptive checkpointing.
                    if iter % ITER_BETWEEN_CHECKPOINTS == 0 {
                        // Protecting must be conducted in a crash-free section.
                        // Otherwise it may forget to drop acquired hazard slot on crashing.
                        recovery::set_in_write(true);
                        unsafe {
                            let localized = result.protect_with(self);
                            compiler_fence(Ordering::SeqCst);

                            if self.is_ejected() {
                                // While protecting, we are ejected.
                                // Then the protection may not be valid.
                                // Drop the shields and restart this read phase manually.
                                drop(localized);
                                recovery::set_restartable(false);
                                recovery::perform_longjmp();
                            } else {
                                // We are not ejected so the protection was valid!
                                // Drop the previous shields and save the current one on the backup storage.
                                if *backup_exist {
                                    // TODO(@jeonghyeon): On each checkpointing, we drop the previous shields and
                                    //                    create shields again. Optimize this by recycling them.
                                    drop_in_place((*backup_shield).as_mut_ptr());
                                }
                                *backup_result = result.clone();
                                *backup_exist = true;
                                write_volatile((*backup_shield).as_mut_ptr(), localized);
                            }
                        }
                        recovery::set_in_write(false);
                    }
                }
            }
        }
        compiler_fence(Ordering::SeqCst);

        // Finaly, close this read phase by unsetting the `RESTARTABLE`.
        recovery::set_restartable(false);

        // Protecting must be conducted in a crash-free section.
        // Otherwise it may forget to drop acquired hazard slot on crashing.
        recovery::set_in_write(true);
        let localized = result.protect_with(self);
        compiler_fence(Ordering::SeqCst);
        if unsafe { self.is_ejected() } {
            drop(localized);
            unsafe { recovery::perform_longjmp() };
        }

        // Free the memory location for the backup storage.
        // If there are backup shields, drop them.
        unsafe {
            let backup_exist = *Box::from_raw(backup_exist);
            if backup_exist {
                drop_in_place((*backup_shield).as_mut_ptr());
            }
            drop(Box::from_raw(backup_result));
            drop(Box::from_raw(backup_shield));
        }

        localized
    }
}

impl Drop for EpochGuard {
    #[inline]
    fn drop(&mut self) {
        if let Some(local) = unsafe { self.local.as_ref() } {
            local.unpin();
        }
    }
}

impl fmt::Debug for EpochGuard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad("Guard { .. }")
    }
}

/// Returns a reference to a dummy guard that allows unprotected access to [`Atomic`]s.
///
/// This guard should be used in special occasions only. Note that it doesn't actually keep any
/// thread pinned - it's just a fake guard that allows loading from [`Atomic`]s unsafely.
///
/// Note that calling [`defer`] with a dummy guard will not defer the function - it will just
/// execute the function immediately.
///
/// # Safety
///
/// Loading and dereferencing data from an [`Atomic`] using this guard is safe only if the
/// [`Atomic`] is not being concurrently modified by other threads.
///
/// # Examples
///
/// ```
/// use crossbeam_cbr_epoch::{self as epoch, Atomic};
/// use std::sync::atomic::Ordering::Relaxed;
///
/// let a = Atomic::new(7);
///
/// unsafe {
///     // Load `a` without pinning the current thread.
///     a.load(Relaxed, epoch::unprotected());
///
///     epoch::unprotected().defer(move || {
///         println!("This gets executed immediately.");
///     });
///
///     // Dropping `dummy` doesn't affect the current thread - it's just a noop.
/// }
/// ```
///
/// The most common use of this function is when constructing or destructing a data structure.
///
/// For example, we can use a dummy guard in the destructor of a Treiber stack because at that
/// point no other thread could concurrently modify the [`Atomic`]s we are accessing.
///
/// If we were to actually pin the current thread during destruction, that would just unnecessarily
/// delay garbage collection and incur some performance cost, so in cases like these `unprotected`
/// is very helpful.
///
/// ```
/// use crossbeam_cbr_epoch::{self as epoch, Atomic};
/// use std::mem::ManuallyDrop;
/// use std::sync::atomic::Ordering::Relaxed;
///
/// struct Stack<T> {
///     head: Atomic<Node<T>>,
/// }
///
/// struct Node<T> {
///     data: ManuallyDrop<T>,
///     next: Atomic<Node<T>>,
/// }
///
/// impl<T> Drop for Stack<T> {
///     fn drop(&mut self) {
///         unsafe {
///             // Unprotected load.
///             let mut node = self.head.load(Relaxed, epoch::unprotected());
///
///             while let Some(n) = node.as_ref() {
///                 // Unprotected load.
///                 let next = n.next.load(Relaxed, epoch::unprotected());
///
///                 // Take ownership of the node, then drop its data and deallocate it.
///                 let mut o = node.into_owned();
///                 ManuallyDrop::drop(&mut o.data);
///                 drop(o);
///
///                 node = next;
///             }
///         }
///     }
/// }
/// ```
///
/// [`Atomic`]: struct.Atomic.html
/// [`defer`]: struct.Guard.html#method.defer
#[inline]
pub unsafe fn unprotected() -> &'static mut EpochGuard {
    // HACK(stjepang): An unprotected guard is just a `Guard` with its field `local` set to null.
    // Since this function returns a `'static` reference to a `Guard`, we must return a reference
    // to a global guard. However, it's not possible to create a `static` `Guard` because it does
    // not implement `Sync`. To get around the problem, we create a static `usize` initialized to
    // zero and then transmute it into a `Guard`. This is safe because `usize` and `Guard`
    // (consisting of a single pointer) have the same representation in memory.
    static UNPROTECTED: usize = 0;
    &mut *(&UNPROTECTED as *const _ as *const _ as *mut EpochGuard)
}

pub enum ReadStatus {
    Finished,
    Continue,
}

pub struct ReadGuard {
    inner: *const EpochGuard,
}

impl ReadGuard {
    fn new(guard: &EpochGuard) -> Self {
        Self { inner: guard }
    }

    pub fn write<'r, F, P>(&'r self, to_deref: P, f: F)
    where
        F: Fn(&P::Localized, &WriteGuard),
        P: Localizable<'r>,
    {
        // Protecting must be conducted in a crash-free section.
        // Otherwise it may forget to drop acquired hazard slot on crashing.
        recovery::set_in_write(true);
        let localized = to_deref.protect_with(unsafe { &*self.inner });
        compiler_fence(Ordering::SeqCst);
        if unsafe { (&*self.inner).is_ejected() } {
            // While protecting, we are ejected.
            // Then the protection may not be valid.
            // Drop the shields and restart this read phase manually.
            drop(localized);
            recovery::set_restartable(false);
            unsafe { recovery::perform_longjmp() };
        }

        // We are not ejected so the protection was valid!
        // Now we are free to call the write phase body.
        let guard = WriteGuard::new::<P>(&localized, unsafe { &*self.inner });
        f(&localized, &guard);
        compiler_fence(Ordering::SeqCst);

        drop(localized);
        recovery::set_in_write(false);

        if unsafe { (&*self.inner).is_ejected() } {
            recovery::set_restartable(false);
            unsafe { recovery::perform_longjmp() };
        }
    }
}

pub struct WriteGuard {
    inner: *mut EpochGuard,
    localized_ptr: *mut u8,
    localized_drop: unsafe fn(*mut u8),
}

impl WriteGuard {
    fn new<'r, P>(localized: &P::Localized, guard: &EpochGuard) -> Self
    where
        P: Localizable<'r>,
    {
        unsafe fn drop_localized<T>(ptr: *mut u8) {
            drop_in_place(ptr as *mut T);
        }
        Self {
            inner: unsafe { guard as *const EpochGuard }.cast_mut(),
            localized_ptr: localized as *const _ as *mut _,
            localized_drop: drop_localized::<P::Localized>,
        }
    }

    pub fn restart_read(&self) -> ! {
        unsafe {
            (self.localized_drop)(self.localized_ptr);
            recovery::set_restartable(false);
            recovery::perform_longjmp()
        }
    }
}

pub trait Writable {
    unsafe fn defer_decrement<F: FnOnce()>(&self, f: F);
    fn defend<T>(&mut self, link: &AtomicUsize, shield: &mut Shield<T>);
    fn copy<T>(&mut self, src: &Shield<T>, dst: &mut Shield<T>);
    unsafe fn as_epoch_guard<'g>(&'g mut self) -> &'g mut EpochGuard;
}

impl Writable for EpochGuard {
    unsafe fn defer_decrement<F: FnOnce()>(&self, f: F) {
        self.defer_unchecked(f);
    }

    fn defend<T>(&mut self, link: &AtomicUsize, shield: &mut Shield<T>) {
        loop {
            let ptr = link.load(Ordering::Acquire);
            if shield.defend_usize(ptr, self).is_ok() {
                return;
            }
            self.repin();
        }
    }

    fn copy<T>(&mut self, src: &Shield<T>, dst: &mut Shield<T>) {
        while dst.defend_usize(src.data, self).is_err() {
            self.repin();
        }
    }

    unsafe fn as_epoch_guard<'g>(&'g mut self) -> &'g mut EpochGuard {
        self
    }
}

impl Writable for WriteGuard {
    unsafe fn defer_decrement<F: FnOnce()>(&self, f: F) {
        unsafe { &mut *self.inner }.defer_unchecked(f);
    }

    fn defend<T>(&mut self, link: &AtomicUsize, shield: &mut Shield<T>) {
        unsafe { &mut *self.inner }.defend(link, shield)
    }

    fn copy<T>(&mut self, src: &Shield<T>, dst: &mut Shield<T>) {
        unsafe { &mut *self.inner }.copy(src, dst)
    }

    unsafe fn as_epoch_guard<'g>(&'g mut self) -> &'g mut EpochGuard {
        unsafe { &mut *self.inner }
    }
}
