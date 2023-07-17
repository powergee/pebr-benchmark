use std::sync::atomic::{fence, AtomicUsize, Ordering};

use hp_sharp::{
    Atomic, CrashGuard, EpochGuard, Handle, Invalidate, Owned, Pointer, Protector, Retire, Shared,
    Shield, WriteResult,
};

use super::concurrent_map::{ConcurrentMap, OutputHolder};

const MAX_HEIGHT: usize = 32;

type Tower<K, V> = [Atomic<Node<K, V>>; MAX_HEIGHT];

// `#[repr(C)]` is used to ensure the first field
// is also the first data in the memory alignment.
#[repr(C)]
struct Node<K, V> {
    next: Tower<K, V>,
    key: K,
    value: V,
    height: usize,
    refs: AtomicUsize,
}

impl<K, V> Node<K, V> {
    pub fn new(key: K, value: V, init_refs: usize) -> Self {
        let height = Self::generate_height();
        Self {
            key,
            value,
            next: Default::default(),
            height,
            refs: AtomicUsize::new(init_refs),
        }
    }

    fn generate_height() -> usize {
        // returns 1 with probability 3/4
        if rand::random::<usize>() % 4 < 3 {
            return 1;
        }
        // returns h with probability 2^(−(h+1))
        let mut height = 2;
        while height < MAX_HEIGHT && rand::random::<bool>() {
            height += 1;
        }
        height
    }

    pub fn decrement<G: Retire>(&self, guard: &mut G) {
        if self.refs.fetch_sub(1, Ordering::Release) == 1 {
            fence(Ordering::Acquire);
            unsafe {
                guard.retire(Shared::<'_, Node<K, V>>::from_usize(
                    self as *const _ as usize,
                ))
            };
        }
    }

    pub fn mark_tower(&self, handle: &Handle) -> bool {
        for level in (0..self.height).rev() {
            let tag = self.next[level].fetch_or(1, Ordering::SeqCst, handle).tag();
            // If the level 0 pointer was already marked, somebody else removed the node.
            if level == 0 && tag != 0 {
                return false;
            }
        }
        true
    }
}

impl<K, V> Invalidate for Node<K, V> {
    fn invalidate(&self) {
        let guard = unsafe { EpochGuard::unprotected() };
        let ptr = self.next[0].load(Ordering::Acquire, &guard);
        self.next[0].store(ptr.with_tag(1 | 2), Ordering::Release, &unsafe {
            CrashGuard::unprotected()
        });
    }

    fn is_invalidated(&self, guard: &hp_sharp::EpochGuard) -> bool {
        (self.next[0].load(Ordering::Acquire, guard).tag() & 2) != 0
    }
}

pub struct Cursor<K, V> {
    preds: [Shield<Node<K, V>>; MAX_HEIGHT],
    succs: [Shield<Node<K, V>>; MAX_HEIGHT],
    found: Shield<Node<K, V>>,
}

impl<K, V> Cursor<K, V>
where
    K: Ord,
{
    fn found(&self, key: &K) -> Option<&Node<K, V>> {
        let node = self.found.as_ref()?;
        if node.key.eq(key) {
            Some(node)
        } else {
            None
        }
    }
}

impl<K, V> OutputHolder<V> for Cursor<K, V> {
    fn default(handle: &mut Handle) -> Self {
        Self::empty(handle)
    }

    fn output(&self) -> &V {
        self.found.as_ref().map(|node| &node.value).unwrap()
    }
}

impl<K, V> Protector for Cursor<K, V> {
    type Target<'r> = SharedCursor<'r, K, V>;

    fn empty(handle: &mut Handle) -> Self {
        Self {
            preds: Protector::empty(handle),
            succs: Protector::empty(handle),
            found: Shield::empty(handle),
        }
    }

    fn protect_unchecked(&mut self, read: &Self::Target<'_>) {
        for i in 0..MAX_HEIGHT {
            self.preds[i].protect_unchecked(&read.preds[i]);
            self.succs[i].protect_unchecked(&read.succs[i]);
        }
        self.found.protect_unchecked(&read.found);
    }

    fn as_target<'r>(&self, guard: &'r hp_sharp::EpochGuard) -> Option<Self::Target<'r>> {
        Some(SharedCursor {
            preds: self.preds.as_target(guard)?,
            succs: self.succs.as_target(guard)?,
            found: self.found.as_target(guard)?,
        })
    }

    fn release(&mut self) {
        for i in 0..MAX_HEIGHT {
            self.preds[i].release();
            self.succs[i].release();
        }
        self.found.release();
    }
}

pub struct SharedCursor<'r, K, V> {
    preds: [Shared<'r, Node<K, V>>; MAX_HEIGHT],
    succs: [Shared<'r, Node<K, V>>; MAX_HEIGHT],
    found: Shared<'r, Node<K, V>>,
}

impl<'r, K, V> Clone for SharedCursor<'r, K, V> {
    fn clone(&self) -> Self {
        Self {
            preds: self.preds.clone(),
            succs: self.succs.clone(),
            found: self.found.clone(),
        }
    }
}

impl<'r, K, V> Copy for SharedCursor<'r, K, V> {}

impl<'r, K, V> SharedCursor<'r, K, V> {
    fn new(head: &Tower<K, V>, _: &'r EpochGuard) -> Self {
        let preds = [unsafe { Shared::from_usize(head as *const _ as usize) }; MAX_HEIGHT];
        let succs = Default::default();
        let found = Default::default();

        Self {
            preds,
            succs,
            found,
        }
    }
}

pub struct SkipList<K, V> {
    head: Tower<K, V>,
}

impl<K, V> Drop for SkipList<K, V> {
    fn drop(&mut self) {
        let guard = unsafe { EpochGuard::unprotected() };
        let mut node = self.head[0].load(Ordering::Relaxed, &guard);

        while let Some(node_ref) = node.as_ref(&guard) {
            let next = node_ref.next[0].load(Ordering::Relaxed, &guard);
            drop(unsafe { node.into_owned() });
            node = next;
        }
    }
}

impl<K, V> SkipList<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    pub fn new() -> Self {
        Self {
            head: Default::default(),
        }
    }

    #[inline(never)]
    fn find_optimistic_inner<'r>(&self, key: &K, guard: &'r EpochGuard) -> SharedCursor<'r, K, V> {
        let mut cursor = SharedCursor::new(&self.head, guard);

        let mut level = MAX_HEIGHT;
        while level >= 1
            && self.head[level - 1]
                .load(Ordering::Relaxed, guard)
                .is_null()
        {
            level -= 1;
        }

        let mut pred = &self.head;
        while level >= 1 {
            level -= 1;
            let mut curr = pred[level].load(Ordering::Acquire, guard);

            loop {
                let curr_node = some_or!(curr.as_ref(guard), break);
                match curr_node.key.cmp(key) {
                    std::cmp::Ordering::Less => {
                        pred = &curr_node.next;
                        curr = curr_node.next[level].load(Ordering::Acquire, guard);
                    }
                    std::cmp::Ordering::Equal => {
                        if curr_node.next[level].load(Ordering::Acquire, guard).tag() == 0 {
                            cursor.found = curr;
                        }
                        return cursor;
                    }
                    std::cmp::Ordering::Greater => break,
                }
            }
        }

        cursor
    }

    fn find_optimistic(&self, key: &K, cursor: &mut Cursor<K, V>, handle: &mut Handle) {
        unsafe {
            cursor.traverse(handle, |guard| self.find_optimistic_inner(key, guard));
        }
    }

    #[inline(never)]
    fn find_inner<'r>(&self, key: &K, guard: &'r EpochGuard) -> Option<SharedCursor<'r, K, V>> {
        let mut cursor = SharedCursor::new(&self.head, guard);

        let mut level = MAX_HEIGHT;
        while level >= 1
            && self.head[level - 1]
                .load(Ordering::Relaxed, guard)
                .is_null()
        {
            level -= 1;
        }

        let mut pred =
            unsafe { Shared::<'_, Node<K, V>>::from_usize(&self.head as *const _ as usize) };
        while level >= 1 {
            level -= 1;
            let mut curr =
                unsafe { pred.deref_unchecked() }.next[level].load(Ordering::Acquire, guard);
            // If `curr` is marked, that means `pred` is removed and we have to restart
            // the search.
            if curr.tag() != 0 {
                return None;
            }

            while let Some(curr_ref) = curr.as_ref(guard) {
                let succ = curr_ref.next[level].load(Ordering::Acquire, guard);

                if succ.tag() != 0 {
                    guard.mask::<_, Shield<Node<K, V>>>(pred, |pred, guard| {
                        match unsafe { pred.deref_unchecked() }.next[level].compare_exchange(
                            curr.with_tag(0),
                            succ.with_tag(0),
                            Ordering::Release,
                            Ordering::Relaxed,
                            guard,
                        ) {
                            Ok(_) => {
                                unsafe { curr.deref_unchecked() }.decrement(guard);
                                return WriteResult::Finished;
                            }
                            Err(_) => {
                                // On failure, we cannot do anything reasonable to
                                // continue searching from the current position.
                                // Restart the search.
                                return WriteResult::RepinEpoch;
                            }
                        }
                    });
                    curr = succ.with_tag(0);
                    continue;
                }

                // If `curr` contains a key that is greater than or equal to `key`, we're
                // done with this level.
                match curr_ref.key.cmp(key) {
                    std::cmp::Ordering::Greater => break,
                    std::cmp::Ordering::Equal => {
                        cursor.found = curr;
                        break;
                    }
                    std::cmp::Ordering::Less => {}
                }

                // Move one step forward.
                pred = curr;
                curr = succ;
            }

            cursor.preds[level] = pred;
            cursor.succs[level] = curr;
        }
        Some(cursor)
    }

    fn find(&self, key: &K, cursor: &mut Cursor<K, V>, handle: &mut Handle) {
        unsafe {
            cursor.traverse(handle, |guard| loop {
                if let Some(cursor) = self.find_inner(key, guard) {
                    return cursor;
                }
            })
        }
    }

    fn insert(&self, key: K, value: V, cursor: &mut Cursor<K, V>, handle: &mut Handle) -> bool {
        self.find(&key, cursor, handle);
        if cursor.found(&key).is_some() {
            return false;
        }

        // The reference count is initially two to account for
        // 1. The link at the level 0 of the tower.
        // 2. The current reference in this function.
        let new_node = Owned::new(Node::new(key, value, 2)).into_shared();
        let new_node_ref = unsafe { new_node.deref_unchecked() };
        let height = new_node_ref.height;

        loop {
            new_node_ref.next[0].store(cursor.succs[0].shared(), Ordering::Relaxed, handle);

            if unsafe { cursor.preds[0].deref_unchecked() }.next[0]
                .compare_exchange(
                    cursor.succs[0].shared(),
                    new_node,
                    Ordering::SeqCst,
                    Ordering::SeqCst,
                    handle,
                )
                .is_ok()
            {
                break;
            }

            // We failed. Let's search for the key and try again.
            self.find(&new_node_ref.key, cursor, handle);
            if cursor.found(&new_node_ref.key).is_some() {
                drop(unsafe { new_node.into_owned() });
                return false;
            }
        }

        // The new node was successfully installed.
        // Build the rest of the tower above level 0.
        let guard = unsafe { &EpochGuard::unprotected() };
        'build: for level in 1..height {
            loop {
                let pred = &cursor.preds[level];
                let succ = &cursor.succs[level];
                let next = new_node_ref.next[level].load(Ordering::SeqCst, guard);

                // If the current pointer is marked, that means another thread is already
                // removing the node we've just inserted. In that case, let's just stop
                // building the tower.
                if next.tag() != 0 {
                    break 'build;
                }

                if succ.as_ref().map(|node| &node.key) == Some(&new_node_ref.key) {
                    self.find(&new_node_ref.key, cursor, handle);
                    continue;
                }

                if new_node_ref.next[level]
                    .compare_exchange(
                        next,
                        succ.shared(),
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                        handle,
                    )
                    .is_err()
                {
                    break 'build;
                }

                new_node_ref.refs.fetch_add(1, Ordering::Relaxed);
                // Try installing the new node at the current level.
                if unsafe { pred.deref_unchecked() }.next[level]
                    .compare_exchange(
                        succ.shared(),
                        new_node,
                        Ordering::SeqCst,
                        Ordering::SeqCst,
                        handle,
                    )
                    .is_ok()
                {
                    // Success! Continue on the next level.
                    break;
                }

                // Installation failed.
                new_node_ref.refs.fetch_sub(1, Ordering::Relaxed);
                self.find(&new_node_ref.key, cursor, handle);
            }
        }

        if new_node_ref.next[height - 1]
            .load(Ordering::SeqCst, guard)
            .tag()
            != 0
        {
            self.find(&new_node_ref.key, cursor, handle);
        }

        new_node_ref.decrement(handle);
        true
    }

    fn remove(&self, key: &K, cursor: &mut Cursor<K, V>, handle: &mut Handle) -> bool {
        loop {
            self.find(key, cursor, handle);
            let node: &Node<K, V> = some_or!(cursor.found(key), return false);

            // Try removing the node by marking its tower.
            if node.mark_tower(handle) {
                for level in (0..node.height).rev() {
                    let succ = node.next[level]
                        .load(Ordering::SeqCst, unsafe { &EpochGuard::unprotected() });

                    // Try linking the predecessor and successor at this level.
                    if unsafe { cursor.preds[level].deref_unchecked() }.next[level]
                        .compare_exchange(
                            unsafe { Shared::from_usize(node as *const _ as usize) },
                            succ.with_tag(0),
                            Ordering::SeqCst,
                            Ordering::SeqCst,
                            handle,
                        )
                        .is_ok()
                    {
                        node.decrement(handle);
                    } else {
                        self.find(key, cursor, handle);
                        break;
                    }
                }
            }
            return true;
        }
    }
}

impl<K, V> ConcurrentMap<K, V> for SkipList<K, V>
where
    K: Ord + Clone,
    V: Clone,
{
    type Output = Cursor<K, V>;

    fn new() -> Self {
        SkipList::new()
    }

    fn get(&self, key: &K, output: &mut Self::Output, handle: &mut Handle) -> bool {
        self.find_optimistic(key, output, handle);
        output.found(key).is_some()
    }

    fn insert(&self, key: K, value: V, output: &mut Self::Output, handle: &mut Handle) -> bool {
        self.insert(key, value, output, handle)
    }

    fn remove<'domain, 'hp>(
        &self,
        key: &K,
        output: &mut Self::Output,
        handle: &mut Handle,
    ) -> bool {
        self.remove(key, output, handle)
    }
}

#[cfg(test)]
mod tests {
    use super::SkipList;
    use crate::hp_sharp::concurrent_map;

    #[test]
    fn smoke_skip_list() {
        concurrent_map::tests::smoke::<SkipList<i32, String>>();
    }
}
