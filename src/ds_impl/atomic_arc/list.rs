use super::concurrent_map::{ConcurrentMap, OutputHolder};
use atomic_arc::{Arc, ArcCell, OptionalArcCell};
use core::cmp::Ordering::{Equal, Greater, Less};

pub struct Node<K, V> {
    next: OptionalArcCell<Self>,
    key: K,
    value: V,
}

struct List<K, V> {
    head: ArcCell<Node<K, V>>,
}

impl<K, V> Drop for List<K, V> {
    fn drop(&mut self) {
        // Manual drop procedure to prevent a stack overflow.
        let prev = self.head.load();
        while let Some(curr) = prev.next.load() {
            prev.next.store(curr.next.load().as_ref());
        }
    }
}

impl<K, V> Default for List<K, V>
where
    K: Ord + Default,
    V: Default,
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
            next: OptionalArcCell::null(),
            key,
            value,
        }
    }

    /// Creates a dummy head.
    /// We never deref key and value of this head node.
    fn head() -> Self {
        Self {
            next: OptionalArcCell::null(),
            key: K::default(),
            value: V::default(),
        }
    }
}

pub struct Cursor<K, V> {
    // The previous node of `curr`.
    prev: Arc<Node<K, V>>,
    // Tag of `curr` should always be zero so when `curr` is stored in a `prev`, we don't store a
    // tagged pointer and cause cleanup to fail.
    curr: Option<Arc<Node<K, V>>>,
}

impl<K, V> OutputHolder<V> for Cursor<K, V> {
    fn output(&self) -> &V {
        self.curr.as_ref().map(|node| &node.value).unwrap()
    }
}

impl<K, V> Cursor<K, V> {
    /// Creates a cursor.
    fn new(head: &ArcCell<Node<K, V>>) -> Self {
        let prev = head.load();
        let curr = prev.next.load();
        Self { prev, curr }
    }
}

impl<K: Ord, V> Cursor<K, V> {
    /// Clean up a chain of logically removed nodes in each traversal.
    #[inline]
    fn find_harris(&mut self, key: &K) -> Option<bool> {
        // Finding phase
        // - cursor.curr: first untagged node w/ key >= search key (4)
        // - cursor.prev: the ref of .next in previous untagged node (1 -> 2)
        // 1 -> 2 -x-> 3 -x-> 4 -> 5 -> ∅  (search key: 4)
        let mut prev_next = self.curr.clone();
        let found = loop {
            let Some(curr_node) = self.curr.as_ref() else {
                break false;
            };
            let (next, next_tag) = curr_node.next.load_with_tag();

            if next_tag != 0 {
                // We do not store tag so that `self.curr`s tag is always 0.
                self.curr = next;
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    self.prev = self.curr.clone().unwrap();
                    self.curr = next.clone();
                    prev_next = next;
                }
                Equal => break true,
                Greater => break false,
            }
        };

        // If prev and curr WERE adjacent, no need to clean up
        if prev_next.as_ref().map(|p| p.as_arc_ptr()) == self.curr.as_ref().map(|p| p.as_arc_ptr())
        {
            return Some(found);
        }

        // cleanup tagged nodes between anchor and curr
        if !self
            .prev
            .next
            .compare_and_set(prev_next.as_ref(), self.curr.as_ref())
        {
            return None;
        }

        Some(found)
    }

    /// Clean up a single logically removed node in each traversal.
    #[inline]
    fn find_harris_michael(&mut self, key: &K) -> Option<bool> {
        loop {
            let Some(curr_node) = self.curr.as_ref() else {
                return Some(false);
            };
            let (next, next_tag) = curr_node.next.load_with_tag();

            if next_tag != 0 {
                if !self
                    .prev
                    .next
                    .compare_and_set(self.curr.as_ref(), next.as_ref())
                {
                    return None;
                }
                self.curr = next;
                continue;
            }

            match curr_node.key.cmp(key) {
                Less => {
                    self.prev = self.curr.clone().unwrap();
                    self.curr = next;
                }
                Equal => return Some(true),
                Greater => return Some(false),
            }
        }
    }

    /// Gotta go fast. Doesn't fail.
    #[inline]
    fn find_harris_herlihy_shavit(&mut self, key: &K) -> Option<bool> {
        Some(loop {
            let Some(curr_node) = self.curr.as_ref() else {
                break false;
            };
            let (next, next_tag) = curr_node.next.load_with_tag();
            match curr_node.key.cmp(key) {
                Less => self.curr = next,
                Equal => break next_tag == 0,
                Greater => break false,
            }
        })
    }

    /// Inserts a value.
    #[inline]
    pub fn insert(&self, node: &Arc<Node<K, V>>) -> bool {
        node.next.store(self.curr.as_ref());

        self.prev
            .next
            .compare_and_set(self.curr.as_ref(), Some(node))
    }

    /// Removes the current node.
    #[inline]
    pub fn remove(&self) -> bool {
        let curr_node = self.curr.as_ref().unwrap();

        let next = curr_node.next.load();
        if !curr_node
            .next
            .compare_and_set_with_tag(next.as_ref(), 0, next.as_ref(), 1)
        {
            return false;
        }

        let _ = self
            .prev
            .next
            .compare_and_set(self.curr.as_ref(), next.as_ref());

        true
    }
}

impl<K, V> List<K, V>
where
    K: Ord + Default,
    V: Default,
{
    /// Creates a new list.
    pub fn new() -> Self {
        List {
            head: ArcCell::new(Node::head()),
        }
    }

    #[inline]
    fn get<F>(&self, key: &K, find: F) -> (bool, Cursor<K, V>)
    where
        F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
    {
        loop {
            let mut cursor = Cursor::new(&self.head);
            if let Some(r) = find(&mut cursor, key) {
                return (r, cursor);
            }
        }
    }

    #[inline]
    fn insert<F>(&self, key: K, value: V, find: F) -> Result<(), Cursor<K, V>>
    where
        F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
    {
        let node = Arc::new(Node::new(key, value));
        loop {
            let (found, cursor) = self.get(&node.key, &find);
            if found {
                return Err(cursor);
            }

            if cursor.insert(&node) {
                return Ok(());
            }
        }
    }

    #[inline]
    fn remove<F>(&self, key: &K, find: F) -> Option<Cursor<K, V>>
    where
        F: Fn(&mut Cursor<K, V>, &K) -> Option<bool>,
    {
        loop {
            let (found, cursor) = self.get(key, &find);
            if !found {
                return None;
            }

            if cursor.remove() {
                return Some(cursor);
            }
        }
    }

    pub fn harris_get(&self, key: &K) -> Option<Cursor<K, V>> {
        let (found, cursor) = self.get(key, Cursor::find_harris);
        if found {
            Some(cursor)
        } else {
            None
        }
    }

    pub fn harris_insert(&self, key: K, value: V) -> Result<(), Cursor<K, V>> {
        self.insert(key, value, Cursor::find_harris)
    }

    pub fn harris_remove(&self, key: &K) -> Option<Cursor<K, V>> {
        self.remove(key, Cursor::find_harris)
    }

    pub fn harris_michael_get(&self, key: &K) -> Option<Cursor<K, V>> {
        let (found, cursor) = self.get(key, Cursor::find_harris_michael);
        if found {
            Some(cursor)
        } else {
            None
        }
    }

    pub fn harris_michael_insert(&self, key: K, value: V) -> Result<(), Cursor<K, V>> {
        self.insert(key, value, Cursor::find_harris_michael)
    }

    pub fn harris_michael_remove(&self, key: &K) -> Option<Cursor<K, V>> {
        self.remove(key, Cursor::find_harris_michael)
    }

    pub fn harris_herlihy_shavit_get(&self, key: &K) -> Option<Cursor<K, V>> {
        let (found, cursor) = self.get(key, Cursor::find_harris_herlihy_shavit);
        if found {
            Some(cursor)
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
    K: Ord + Default,
    V: Default,
{
    type Output = Cursor<K, V>;

    fn new() -> Self {
        HList { inner: List::new() }
    }

    #[inline(always)]
    fn get(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_get(key)
    }
    #[inline(always)]
    fn insert(&self, key: K, value: V) -> Result<(), Self::Output> {
        self.inner.harris_insert(key, value)
    }
    #[inline(always)]
    fn remove(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_remove(key)
    }
}

pub struct HMList<K, V> {
    inner: List<K, V>,
}

impl<K, V> ConcurrentMap<K, V> for HMList<K, V>
where
    K: Ord + Default,
    V: Default,
{
    type Output = Cursor<K, V>;

    fn new() -> Self {
        HMList { inner: List::new() }
    }

    #[inline(always)]
    fn get(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_michael_get(key)
    }
    #[inline(always)]
    fn insert(&self, key: K, value: V) -> Result<(), Self::Output> {
        self.inner.harris_michael_insert(key, value)
    }
    #[inline(always)]
    fn remove(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_michael_remove(key)
    }
}

pub struct HHSList<K, V> {
    inner: List<K, V>,
}

impl<K, V> ConcurrentMap<K, V> for HHSList<K, V>
where
    K: Ord + Default,
    V: Default,
{
    type Output = Cursor<K, V>;

    fn new() -> Self {
        HHSList { inner: List::new() }
    }

    #[inline(always)]
    fn get(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_herlihy_shavit_get(key)
    }
    #[inline(always)]
    fn insert(&self, key: K, value: V) -> Result<(), Self::Output> {
        self.inner.harris_insert(key, value)
    }
    #[inline(always)]
    fn remove(&self, key: &K) -> Option<Self::Output> {
        self.inner.harris_remove(key)
    }
}

#[cfg(test)]
mod tests {
    use super::{HHSList, HList, HMList};
    use crate::ds_impl::atomic_arc::concurrent_map;

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
}
