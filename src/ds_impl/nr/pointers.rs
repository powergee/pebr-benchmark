use portable_atomic::{AtomicU128, Ordering};
use std::{marker::PhantomData, ptr::null_mut};

pub struct CompareExchangeError<T, P: Pointer<T>> {
    pub new: P,
    pub current: Shared<T>,
}

pub struct Atomic<T> {
    link: AtomicU128,
    _marker: PhantomData<*mut T>,
}

unsafe impl<T> Sync for Atomic<T> {}
unsafe impl<T> Send for Atomic<T> {}

fn pack<T>(ptr: *mut T, tag: usize) -> u128 {
    ((ptr as usize as u128) << 64) | (tag as u128)
}

fn unpack<T>(data: u128) -> (*mut T, usize) {
    let mask = (1u128 << 64) - 1;
    (
        ((data & (mask << 64)) >> 64) as usize as *mut T,
        (data & mask) as usize,
    )
}

impl<T> Atomic<T> {
    pub fn new(init: T) -> Self {
        let link = AtomicU128::new(pack(Box::into_raw(Box::new(init)), 0));
        Self {
            link,
            _marker: PhantomData,
        }
    }

    pub fn null() -> Self {
        let link = AtomicU128::new(pack(null_mut::<T>(), 0));
        Self {
            link,
            _marker: PhantomData,
        }
    }

    pub fn load(&self, order: Ordering) -> Shared<T> {
        let (ptr, tag) = unpack(self.link.load(order));
        Shared { ptr, tag }
    }

    pub fn store(&self, ptr: Shared<T>, order: Ordering) {
        self.link.store(pack(ptr.ptr, ptr.tag), order)
    }

    pub fn fetch_or(&self, val: usize, order: Ordering) -> Shared<T> {
        let (ptr, tag) = unpack(self.link.fetch_or(val as u128, order));
        Shared { ptr, tag }
    }

    pub fn compare_exchange<P: Pointer<T>>(
        &self,
        current: Shared<T>,
        new: P,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Shared<T>, CompareExchangeError<T, P>> {
        let current = current.into_raw();
        let new = new.into_raw();

        match self.link.compare_exchange(current, new, success, failure) {
            Ok(current) => {
                let (ptr, tag) = unpack(current);
                Ok(Shared { ptr, tag })
            }
            Err(current) => {
                let new = unsafe { P::from_raw(new) };
                let (ptr, tag) = unpack(current);
                Err(CompareExchangeError {
                    new,
                    current: Shared { ptr, tag },
                })
            }
        }
    }

    pub unsafe fn into_owned(self) -> Box<T> {
        Box::from_raw(unpack(self.link.into_inner()).0)
    }
}

impl<T> Default for Atomic<T> {
    fn default() -> Self {
        Self::null()
    }
}

impl<T> From<Shared<T>> for Atomic<T> {
    fn from(value: Shared<T>) -> Self {
        let link = AtomicU128::new(value.into_raw());
        Self {
            link,
            _marker: PhantomData,
        }
    }
}

pub struct Shared<T> {
    ptr: *mut T,
    tag: usize,
}

impl<T> Shared<T> {
    pub fn from_owned(init: T) -> Shared<T> {
        let ptr = Box::into_raw(Box::new(init));
        Self { ptr, tag: 0 }
    }

    pub unsafe fn into_owned(self) -> T {
        *Box::from_raw(self.ptr)
    }

    pub fn null() -> Self {
        Self {
            ptr: null_mut(),
            tag: 0,
        }
    }

    pub fn tag(&self) -> usize {
        self.tag
    }

    pub fn is_null(&self) -> bool {
        self.ptr.is_null()
    }

    pub fn with_tag(&self, tag: usize) -> Self {
        Self { ptr: self.ptr, tag }
    }

    pub unsafe fn as_ref<'g>(&self) -> Option<&'g T> {
        self.ptr.as_ref()
    }

    pub unsafe fn as_mut<'g>(&self) -> Option<&'g mut T> {
        self.ptr.as_mut()
    }

    pub unsafe fn deref<'g>(&self) -> &'g T {
        &*self.ptr
    }

    pub unsafe fn deref_mut<'g>(&mut self) -> &'g mut T {
        &mut *self.ptr
    }
}

impl<T> From<usize> for Shared<T> {
    fn from(val: usize) -> Self {
        Self {
            ptr: val as *const T as *mut T,
            tag: 0,
        }
    }
}

impl<T> Clone for Shared<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Shared<T> {}

impl<T> PartialEq for Shared<T> {
    fn eq(&self, other: &Self) -> bool {
        self.ptr == other.ptr
    }
}

impl<T> Eq for Shared<T> {}

pub trait Pointer<T> {
    fn into_raw(self) -> u128;
    unsafe fn from_raw(val: u128) -> Self;
}

impl<T> Pointer<T> for Shared<T> {
    fn into_raw(self) -> u128 {
        pack(self.ptr, self.tag)
    }

    unsafe fn from_raw(val: u128) -> Self {
        Shared::from(val as usize)
    }
}

impl<T> Pointer<T> for Box<T> {
    fn into_raw(self) -> u128 {
        pack(Box::into_raw(self), 0)
    }

    unsafe fn from_raw(val: u128) -> Self {
        Box::from_raw(unpack(val).0)
    }
}
