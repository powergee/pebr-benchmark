use super::concurrent_map::{ConcurrentMap, OutputHolder};
use circ::{AtomicRc, Guard, Rc, RcObject, Snapshot};

use std::cmp::Ordering::{Equal, Greater, Less};
use std::sync::atomic::Ordering;

pub struct Node<K, V> {
    next: AtomicRc<Self>,
    key: K,
    value: V,
}

unsafe impl<K, V> RcObject for Node<K, V> {
    fn pop_edges(&mut self, out: &mut Vec<Rc<Self>>) {
        out.push(self.next.take());
    }
}

struct List<K, V> {
    head: AtomicRc<Node<K, V>>,
}

impl<K, V> Default for List<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Node<K, V>
where
    K: Default,
    V: Default,
{
    /// Creates a new node.
    fn new(key: K, value: V) -> Self {
        Self {
            next: AtomicRc::null(),
            key,
            value,
        }
    }

    /// Creates a dummy head.
    /// We never deref key and value of this head node.
    fn head() -> Self {
        Self {
            next: AtomicRc::null(),
            key: K::default(),
            value: V::default(),
        }
    }
}

impl<'g, K, V> OutputHolder<'g, V> for Snapshot<'g, Node<K, V>> {
    fn output(&self) -> &'g V {
        self.as_ref().map(|node| &node.value).unwrap()
    }
}

pub struct Cursor<'g, K, V> {
    // The previous node of `curr`.
    prev: Snapshot<'g, Node<K, V>>,
    // Tag of `curr` should always be zero so when `curr` is stored in a `prev`, we don't store a
    // tagged pointer and cause cleanup to fail.
    curr: Snapshot<'g, Node<K, V>>,
}

impl<'g, K, V> Cursor<'g, K, V> {
    fn new() -> Self {
        Self {
            prev: Snapshot::null(),
            curr: Snapshot::null(),
        }
    }

    /// Initializes a cursor.
    fn initialize(&mut self, head: &AtomicRc<Node<K, V>>, cs: &'g Guard) {
        self.prev = head.load(Ordering::Relaxed, cs);
        self.curr = self
            .prev
            .as_ref()
            .map(|node| node.next.load(Ordering::Acquire, cs))
            .unwrap();
    }
}

impl<'g, K: Ord, V> Cursor<'g, K, V> {
    /// Clean up a chain of logically removed nodes in each traversal.
    #[inline]
    fn find_harris(&mut self, key: &K, cs: &'g Guard) -> Result<bool, ()> {
        let mut prev_next = self.curr;
        let found = loop {
            let curr_node = some_or!(self.curr.as_ref(), break false);
            let mut next = curr_node.next.load(Ordering::Acquire, cs);

            if next.tag() != 0 {
                // We add a 0 tag here so that `self.curr`s tag is always 0.
                next = next.with_tag(0);
                self.curr = next;
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    self.prev = self.curr;
                    self.curr = next;
                    prev_next = next;
                }
                Equal => break true,
                Greater => break false,
            }
        };

        // If prev and curr WERE adjacent, no need to clean up
        if prev_next == self.curr {
            return Ok(found);
        }

        // cleanup tagged nodes between anchor and curr
        self.prev
            .as_ref()
            .unwrap()
            .next
            .compare_exchange(
                prev_next,
                self.curr.counted(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            )
            .map_err(|_| ())?;

        Ok(found)
    }

    /// Clean up a single logically removed node in each traversal.
    #[inline]
    fn find_harris_michael(&mut self, key: &K, cs: &'g Guard) -> Result<bool, ()> {
        loop {
            debug_assert_eq!(self.curr.tag(), 0);

            let curr_node = some_or!(self.curr.as_ref(), return Ok(false));
            let mut next = curr_node.next.load(Ordering::Acquire, cs);

            // NOTE: original version aborts here if self.prev is tagged

            if next.tag() != 0 {
                next = next.with_tag(0);
                self.try_unlink_curr(next, cs)?;
                self.curr = next;
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    self.prev = self.curr;
                    self.curr = next;
                }
                Equal => return Ok(true),
                Greater => return Ok(false),
            }
        }
    }

    /// Gotta go fast. Doesn't fail.
    #[inline]
    fn find_harris_herlihy_shavit(&mut self, key: &K, cs: &'g Guard) -> Result<bool, ()> {
        Ok(loop {
            let curr_node = some_or!(self.curr.as_ref(), break false);
            let next = curr_node.next.load(Ordering::Acquire, cs);
            match curr_node.key.cmp(key) {
                Less => self.curr = next,
                Equal => break next.tag() == 0,
                Greater => break false,
            }
        })
    }

    #[inline]
    fn try_unlink_curr(&self, next: Snapshot<'g, Node<K, V>>, cs: &'g Guard) -> Result<(), ()> {
        self.prev
            .as_ref()
            .unwrap()
            .next
            .compare_exchange(
                self.curr,
                next.counted(),
                Ordering::Release,
                Ordering::Relaxed,
                cs,
            )
            .map(|_| ())
            .map_err(|_| ())
    }

    /// Inserts a value.
    #[inline]
    pub fn insert(&self, node: Rc<Node<K, V>>, cs: &'g Guard) -> Result<(), Rc<Node<K, V>>> {
        node.as_ref()
            .unwrap()
            .next
            .store(self.curr.counted(), Ordering::Relaxed, cs);

        self.prev
            .as_ref()
            .unwrap()
            .next
            .compare_exchange(self.curr, node, Ordering::Release, Ordering::Relaxed, cs)
            .map(|_| ())
            .map_err(|e| e.desired)
    }

    /// removes the current node.
    #[inline]
    pub fn remove(&self, cs: &'g Guard) -> Result<(), ()> {
        let curr_node = self.curr.as_ref().unwrap();

        let next = curr_node.next.load(Ordering::Acquire, cs);
        curr_node
            .next
            .compare_exchange_tag(next.with_tag(0), 1, Ordering::AcqRel, Ordering::Relaxed, cs)
            .map_err(|_| ())?;

        let _ = self.try_unlink_curr(next, cs);

        Ok(())
    }
}

impl<K, V> List<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    /// Creates a new list.
    pub fn new() -> Self {
        List {
            head: AtomicRc::new(Node::head()),
        }
    }

    #[inline]
    fn get<'g, F>(&self, key: &K, find: F, cs: &'g Guard) -> (Cursor<'g, K, V>, bool)
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Guard) -> Result<bool, ()>,
    {
        loop {
            let mut cursor = Cursor::new();
            cursor.initialize(&self.head, cs);
            if let Ok(r) = find(&mut cursor, key, cs) {
                return (cursor, r);
            }
        }
    }

    #[inline]
    fn insert<'g, F>(&self, key: K, value: V, find: F, cs: &'g Guard) -> bool
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Guard) -> Result<bool, ()>,
    {
        let mut node = Rc::new(Node::new(key, value));
        loop {
            let (cursor, found) = self.get(node.as_ref().map(|node| &node.key).unwrap(), &find, cs);
            if found {
                unsafe { node.into_inner() };
                return false;
            }

            match cursor.insert(node, cs) {
                Err(n) => node = n,
                Ok(()) => return true,
            }
        }
    }

    #[inline]
    fn remove<'g, F>(&self, key: &K, find: F, cs: &'g Guard) -> Option<Snapshot<'g, Node<K, V>>>
    where
        F: Fn(&mut Cursor<'g, K, V>, &K, &'g Guard) -> Result<bool, ()>,
    {
        loop {
            let (cursor, found) = self.get(key, &find, cs);
            if !found {
                return None;
            }

            match cursor.remove(cs) {
                Err(()) => continue,
                Ok(_) => return Some(cursor.curr),
            }
        }
    }

    #[inline]
    fn pop<'g>(&self, cs: &'g Guard) -> Option<Snapshot<'g, Node<K, V>>> {
        loop {
            let mut cursor = Cursor::new();
            cursor.initialize(&self.head, cs);
            if cursor.curr.is_null() {
                return None;
            }

            match cursor.remove(cs) {
                Err(()) => continue,
                Ok(_) => return Some(cursor.curr),
            }
        }
    }

    /// Omitted
    pub fn harris_get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Snapshot<'g, Node<K, V>>> {
        let (cursor, found) = self.get(key, Cursor::find_harris, cs);
        if found {
            Some(cursor.curr)
        } else {
            None
        }
    }

    /// Omitted
    pub fn harris_insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.insert(key, value, Cursor::find_harris, cs)
    }

    /// Omitted
    pub fn harris_remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Snapshot<'g, Node<K, V>>> {
        self.remove(key, Cursor::find_harris, cs)
    }

    /// Omitted
    pub fn harris_michael_get<'g>(
        &self,
        key: &K,
        cs: &'g Guard,
    ) -> Option<Snapshot<'g, Node<K, V>>> {
        let (cursor, found) = self.get(key, Cursor::find_harris_michael, cs);
        if found {
            Some(cursor.curr)
        } else {
            None
        }
    }

    /// Omitted
    pub fn harris_michael_insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.insert(key, value, Cursor::find_harris_michael, cs)
    }

    /// Omitted
    pub fn harris_michael_remove<'g>(
        &self,
        key: &K,
        cs: &'g Guard,
    ) -> Option<Snapshot<'g, Node<K, V>>> {
        self.remove(key, Cursor::find_harris_michael, cs)
    }

    /// Omitted
    pub fn harris_herlihy_shavit_get<'g>(
        &self,
        key: &K,
        cs: &'g Guard,
    ) -> Option<Snapshot<'g, Node<K, V>>> {
        let (cursor, found) = self.get(key, Cursor::find_harris_herlihy_shavit, cs);
        if found {
            Some(cursor.curr)
        } else {
            None
        }
    }
}

pub struct HList<K, V> {
    inner: List<K, V>,
}

impl<K, V> ConcurrentMap<K, V> for HList<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    type Output<'g> = Snapshot<'g, Node<K, V>>;

    fn new() -> Self {
        HList { inner: List::new() }
    }

    #[inline(always)]
    fn get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_get(key, cs)
    }
    #[inline(always)]
    fn insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.inner.harris_insert(key, value, cs)
    }
    #[inline(always)]
    fn remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_remove(key, cs)
    }
}

pub struct HMList<K, V> {
    inner: List<K, V>,
}

impl<K, V> HMList<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    /// For optimistic search on HashMap
    #[inline(always)]
    pub fn get_harris_herlihy_shavit<'g>(
        &self,
        key: &K,
        cs: &'g Guard,
    ) -> Option<Snapshot<'g, Node<K, V>>> {
        self.inner.harris_herlihy_shavit_get(key, cs)
    }
}

impl<K, V> ConcurrentMap<K, V> for HMList<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    type Output<'g> = Snapshot<'g, Node<K, V>>;

    fn new() -> Self {
        HMList { inner: List::new() }
    }

    #[inline(always)]
    fn get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_michael_get(key, cs)
    }
    #[inline(always)]
    fn insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.inner.harris_michael_insert(key, value, cs)
    }
    #[inline(always)]
    fn remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_michael_remove(key, cs)
    }
}

pub struct HHSList<K, V> {
    inner: List<K, V>,
}

impl<K, V> HHSList<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    /// Pop the first element efficiently.
    /// This method is used for only the fine grained benchmark (src/bin/long_running).
    pub fn pop<'g>(&self, cs: &'g Guard) -> Option<Snapshot<'g, Node<K, V>>> {
        self.inner.pop(cs)
    }
}

impl<K, V> ConcurrentMap<K, V> for HHSList<K, V>
where
    K: 'static + Ord + Default,
    V: 'static + Default,
{
    type Output<'g> = Snapshot<'g, Node<K, V>>;

    fn new() -> Self {
        HHSList { inner: List::new() }
    }

    #[inline(always)]
    fn get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_herlihy_shavit_get(key, cs)
    }
    #[inline(always)]
    fn insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.inner.harris_insert(key, value, cs)
    }
    #[inline(always)]
    fn remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.inner.harris_remove(key, cs)
    }
}

#[cfg(test)]
mod tests {
    use super::{HHSList, HList, HMList};
    use crate::ds_impl::circ_ebr::concurrent_map;

    #[test]
    fn smoke_h_list() {
        concurrent_map::tests::smoke::<HList<i32, String>>();
    }

    #[test]
    fn smoke_hm_list() {
        concurrent_map::tests::smoke::<HMList<i32, String>>();
    }

    #[test]
    fn smoke_hhs_list() {
        concurrent_map::tests::smoke::<HHSList<i32, String>>();
    }

    #[test]
    fn litmus_hhs_pop() {
        use circ::cs;
        use concurrent_map::ConcurrentMap;
        let map = HHSList::new();

        let cs = &cs();
        map.insert(1, "1", cs);
        map.insert(2, "2", cs);
        map.insert(3, "3", cs);

        assert_eq!(map.pop(cs).unwrap().as_ref().unwrap().value, "1");
        assert_eq!(map.pop(cs).unwrap().as_ref().unwrap().value, "2");
        assert_eq!(map.pop(cs).unwrap().as_ref().unwrap().value, "3");
        assert!(map.pop(cs).is_none());
    }
}
