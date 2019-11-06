use super::concurrent_map::ConcurrentMap;
use crossbeam_pebr::{unprotected, Atomic, Guard, Owned, Pointer, Shared, Shield, ShieldError};

use std::cmp;
use std::mem::{self, ManuallyDrop};
use std::ptr;
use std::sync::atomic::Ordering;

#[derive(Debug)]
struct Node<K, V> {
    // Mark: tag()
    // Tag: not needed
    next: Atomic<Node<K, V>>,

    key: K,

    value: ManuallyDrop<V>,
}

pub struct List<K, V> {
    head: Atomic<Node<K, V>>,
}

impl<K, V> Default for List<K, V>
where
    K: Ord,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Drop for List<K, V> {
    fn drop(&mut self) {
        unsafe {
            let mut curr = self.head.load(Ordering::Relaxed, unprotected());

            while !curr.is_null() {
                let curr_ref = curr.deref_mut();
                let next = curr_ref.next.load(Ordering::Relaxed, unprotected());
                if next.tag() == 0 {
                    ManuallyDrop::drop(&mut curr_ref.value);
                }
                drop(curr.into_owned());
                curr = next;
            }
        }
    }
}

pub struct Cursor<K, V> {
    prev: Shield<Node<K, V>>,
    curr: Shield<Node<K, V>>,
}

impl<K, V> Cursor<K, V> {
    pub fn new(guard: &Guard) -> Self {
        Self {
            prev: Shield::null(guard),
            curr: Shield::null(guard),
        }
    }

    pub fn release(&mut self) {
        self.prev.release();
        self.curr.release();
    }
}

enum FindError {
    Retry,
    ShieldError(ShieldError),
}

impl<K, V> List<K, V>
where
    K: Ord,
{
    pub fn new() -> Self {
        List {
            head: Atomic::null(),
        }
    }

    /// Returns (1) whether it found an entry, and (2) a cursor.
    #[inline(always)]
    fn find_inner<'g>(
        &'g self,
        key: &K,
        cursor: &mut Cursor<K, V>,
        guard: &'g Guard,
    ) -> Result<bool, FindError> {
        // HACK(@jeehoonkang): we're unsafely assuming the first 8 bytes of both `Node<K, V>` and
        // `List<K, V>` are `Atomic<Node<K, V>>`.
        unsafe {
            cursor
                .prev
                .defend_fake(Shared::from_usize(&self.head as *const _ as usize));
        }
        let mut curr = self.head.load(Ordering::Acquire, guard);

        let result = loop {
            debug_assert_eq!(curr.tag(), 0);
            if curr.is_null() {
                unsafe { cursor.curr.defend_fake(curr) };
                break Ok(false);
            }

            cursor
                .curr
                .defend(curr, guard)
                .map_err(FindError::ShieldError)?;
            let curr_node = unsafe { curr.deref() };

            let mut next = curr_node.next.load(Ordering::Acquire, guard);

            if next.tag() == 0 {
                match curr_node.key.cmp(key) {
                    cmp::Ordering::Less => mem::swap(&mut cursor.prev, &mut cursor.curr),
                    cmp::Ordering::Equal => break Ok(true),
                    cmp::Ordering::Greater => break Ok(false),
                }
            } else {
                next = next.with_tag(0);
                if unsafe { cursor.prev.deref() }
                    .next
                    .compare_and_set(curr, next, Ordering::AcqRel, guard)
                    .is_ok()
                {
                    unsafe { guard.defer_destroy(curr) };
                } else {
                    break Err(FindError::Retry);
                }
            }
            curr = next;
        };

        result
    }

    fn find<'g>(&'g self, key: &K, cursor: &mut Cursor<K, V>, guard: &'g mut Guard) -> bool {
        // TODO(@jeehoonkang): we want to use `FindError::retry`, but it requires higher-kinded
        // things...
        loop {
            match self.find_inner(key, cursor, unsafe { &mut *(guard as *mut Guard) }) {
                Ok(r) => return r,
                Err(FindError::Retry) => continue,
                Err(FindError::ShieldError(ShieldError::Ejected)) => guard.repin(),
            }
        }
    }

    pub fn get<'g>(
        &'g self,
        cursor: &'g mut Cursor<K, V>,
        key: &K,
        guard: &'g mut Guard,
    ) -> Option<&'g V> {
        let found = self.find(key, cursor, guard);

        if found {
            Some(unsafe { &cursor.curr.deref().value })
        } else {
            None
        }
    }

    fn insert_inner<'g>(
        &'g self,
        mut node: Shared<'g, Node<K, V>>,
        cursor: &mut Cursor<K, V>,
        guard: &'g Guard,
    ) -> Result<bool, FindError> {
        loop {
            // TODO: create cursor in this function.
            let found = self.find_inner(&unsafe { node.deref() }.key, cursor, guard)?;
            if found {
                unsafe {
                    ManuallyDrop::drop(&mut node.deref_mut().value);
                    drop(node.into_owned());
                }
                return Ok(false);
            }

            unsafe { node.deref() }
                .next
                .store(cursor.curr.shared(), Ordering::Relaxed);
            if unsafe { cursor.prev.deref() }
                .next
                .compare_and_set(cursor.curr.shared(), node, Ordering::AcqRel, guard)
                .is_ok()
            {
                return Ok(true);
            }
        }
    }

    pub fn insert(&self, cursor: &mut Cursor<K, V>, key: K, value: V, guard: &mut Guard) -> bool {
        let node = Owned::new(Node {
            key: key,
            value: ManuallyDrop::new(value),
            next: Atomic::null(),
        })
        .into_shared(unsafe { unprotected() });

        loop {
            match self.insert_inner(node, cursor, unsafe { &mut *(guard as *mut Guard) }) {
                Ok(r) => return r,
                Err(FindError::Retry) => continue,
                Err(FindError::ShieldError(ShieldError::Ejected)) => guard.repin(),
            }
        }
    }

    fn remove_inner<'g>(
        &'g self,
        key: &K,
        cursor: &mut Cursor<K, V>,
        guard: &'g Guard,
    ) -> Result<Option<V>, FindError> {
        loop {
            let found = self.find_inner(key, cursor, guard)?;
            if !found {
                return Ok(None);
            }

            let curr_node = unsafe { cursor.curr.as_ref() }.unwrap();
            let next = curr_node.next.fetch_or(1, Ordering::AcqRel, guard);
            if next.tag() == 1 {
                continue;
            }

            let value = unsafe { ptr::read(&curr_node.value) };

            if unsafe { cursor.prev.deref() }
                .next
                .compare_and_set(cursor.curr.shared(), next, Ordering::AcqRel, guard)
                .is_ok()
            {
                unsafe { guard.defer_destroy(cursor.curr.shared()) };
            }

            return Ok(Some(ManuallyDrop::into_inner(value)));
        }
    }

    pub fn remove(&self, cursor: &mut Cursor<K, V>, key: &K, guard: &mut Guard) -> Option<V> {
        loop {
            match self.remove_inner(key, cursor, unsafe { &mut *(guard as *mut Guard) }) {
                Ok(r) => return r,
                Err(FindError::Retry) => continue,
                Err(FindError::ShieldError(ShieldError::Ejected)) => guard.repin(),
            }
        }
    }
}

impl<K, V> ConcurrentMap<K, V> for List<K, V>
where
    K: Ord + 'static,
    V: 'static,
{
    type Handle = Cursor<K, V>;

    fn new() -> Self {
        Self::new()
    }

    fn handle(guard: &Guard) -> Self::Handle {
        Cursor::new(guard)
    }

    fn clear(handle: &mut Self::Handle) {
        handle.release();
    }

    #[inline]
    fn get<'g>(
        &'g self,
        handle: &'g mut Self::Handle,
        key: &K,
        guard: &'g mut Guard,
    ) -> Option<&'g V> {
        self.get(handle, key, guard)
    }

    #[inline]
    fn insert(&self, handle: &mut Self::Handle, key: K, value: V, guard: &mut Guard) -> bool {
        self.insert(handle, key, value, guard)
    }

    #[inline]
    fn remove(&self, handle: &mut Self::Handle, key: &K, guard: &mut Guard) -> Option<V> {
        self.remove(handle, key, guard)
    }
}

#[cfg(test)]
mod tests {
    use super::List;
    use crate::pebr::concurrent_map;

    #[test]
    fn smoke_list() {
        concurrent_map::tests::smoke::<List<i32, String>>();
    }
}
