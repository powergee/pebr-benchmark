use super::concurrent_map::ConcurrentMap;
use crossbeam_ebr::Guard;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use super::list::HMList;

pub struct HashMap<K, V> {
    buckets: Vec<HMList<K, V>>,
}

impl<K, V> HashMap<K, V>
where
    K: Ord + Hash,
{
    pub fn with_capacity(n: usize) -> Self {
        let mut buckets = Vec::with_capacity(n);
        for _ in 0..n {
            buckets.push(HMList::new());
        }

        HashMap { buckets }
    }

    #[inline]
    pub fn get_bucket(&self, index: usize) -> &HMList<K, V> {
        unsafe { self.buckets.get_unchecked(index % self.buckets.len()) }
    }

    // TODO(@jeehoonkang): we're converting u64 to usize, which may lose information.
    #[inline]
    fn hash(k: &K) -> usize {
        let mut s = DefaultHasher::new();
        k.hash(&mut s);
        s.finish() as usize
    }

    pub fn get<'g>(&'g self, k: &'g K, guard: &'g Guard) -> Option<&'g V> {
        let i = Self::hash(k);
        self.get_bucket(i).get(k, guard)
    }

    pub fn insert(&self, k: K, v: V, guard: &Guard) -> bool {
        let i = Self::hash(&k);
        self.get_bucket(i).insert(k, v, guard)
    }

    pub fn remove(&self, k: &K, guard: &Guard) -> Option<V> {
        let i = Self::hash(&k);
        self.get_bucket(i).remove(k, guard)
    }
}

impl<K, V> ConcurrentMap<K, V> for HashMap<K, V>
where
    K: Ord + Hash,
{
    fn new() -> Self {
        Self::with_capacity(30000)
    }

    #[inline]
    fn get<'g>(&'g self, key: &'g K, guard: &'g Guard) -> Option<&'g V> {
        self.get(key, guard)
    }
    #[inline]
    fn insert(&self, key: K, value: V, guard: &Guard) -> bool {
        self.insert(key, value, guard)
    }
    #[inline]
    fn remove(&self, key: &K, guard: &Guard) -> Option<V> {
        self.remove(key, guard)
    }
}

#[cfg(test)]
mod tests {
    extern crate rand;
    use super::HashMap;
    use crossbeam_utils::thread;
    use rand::prelude::*;

    #[test]
    fn smoke_hashmap() {
        let hash_map = &HashMap::with_capacity(10000);

        // insert
        thread::scope(|s| {
            for t in 0..10 {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> = (0..3000).map(|k| k * 10 + t).collect();
                    keys.shuffle(&mut rng);
                    for i in keys {
                        assert!(hash_map.insert(i, i.to_string(), &crossbeam_ebr::pin()));
                    }
                });
            }
        })
        .unwrap();

        // remove
        thread::scope(|s| {
            for t in 0..5 {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> = (0..3000).map(|k| k * 10 + t).collect();
                    keys.shuffle(&mut rng);
                    for i in keys {
                        assert_eq!(
                            i.to_string(),
                            hash_map.remove(&i, &crossbeam_ebr::pin()).unwrap()
                        );
                    }
                });
            }
        })
        .unwrap();

        // get
        thread::scope(|s| {
            for t in 5..10 {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> = (0..3000).map(|k| k * 10 + t).collect();
                    keys.shuffle(&mut rng);
                    for i in keys {
                        assert_eq!(
                            i.to_string(),
                            *hash_map.get(&i, &crossbeam_ebr::pin()).unwrap()
                        );
                    }
                });
            }
        })
        .unwrap();
    }
}
