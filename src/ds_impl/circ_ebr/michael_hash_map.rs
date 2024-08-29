use super::concurrent_map::ConcurrentMap;
use circ::Guard;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use super::list::HHSList;

pub struct HashMap<K, V> {
    buckets: Vec<HHSList<K, V>>,
}

impl<K, V> HashMap<K, V>
where
    K: Ord + Hash + Default + 'static,
    V: Default + 'static,
{
    pub fn with_capacity(n: usize) -> Self {
        let mut buckets = Vec::with_capacity(n);
        for _ in 0..n {
            buckets.push(HHSList::new());
        }

        HashMap { buckets }
    }

    #[inline]
    pub fn get_bucket(&self, index: usize) -> &HHSList<K, V> {
        unsafe { self.buckets.get_unchecked(index % self.buckets.len()) }
    }

    #[inline]
    fn hash(k: &K) -> usize {
        let mut s = DefaultHasher::new();
        k.hash(&mut s);
        s.finish() as usize
    }

    pub fn get<'g>(
        &self,
        k: &K,
        cs: &'g Guard,
    ) -> Option<<HHSList<K, V> as ConcurrentMap<K, V>>::Output<'g>> {
        let i = Self::hash(k);
        self.get_bucket(i).get(k, cs)
    }

    pub fn insert<'g>(&self, k: K, v: V, cs: &'g Guard) -> bool {
        let i = Self::hash(&k);
        self.get_bucket(i).insert(k, v, cs)
    }

    pub fn remove<'g>(
        &self,
        k: &K,
        cs: &'g Guard,
    ) -> Option<<HHSList<K, V> as ConcurrentMap<K, V>>::Output<'g>> {
        let i = Self::hash(k);
        self.get_bucket(i).remove(k, cs)
    }
}

impl<K, V> ConcurrentMap<K, V> for HashMap<K, V>
where
    K: Ord + Hash + Default + 'static,
    V: Default + 'static,
{
    type Output<'g> = <HHSList<K, V> as ConcurrentMap<K, V>>::Output<'g>;

    fn new() -> Self {
        Self::with_capacity(30000)
    }

    #[inline(always)]
    fn get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.get(key, cs)
    }
    #[inline(always)]
    fn insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool {
        self.insert(key, value, cs)
    }
    #[inline(always)]
    fn remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>> {
        self.remove(key, cs)
    }
}

#[cfg(test)]
mod tests {
    use super::HashMap;
    use crate::ds_impl::circ_ebr::concurrent_map;

    #[test]
    fn smoke_hashmap() {
        concurrent_map::tests::smoke::<HashMap<i32, String>>();
    }
}
