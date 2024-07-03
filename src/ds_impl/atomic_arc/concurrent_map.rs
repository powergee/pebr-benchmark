pub trait OutputHolder<V> {
    fn output(&self) -> &V;
}

pub trait ConcurrentMap<K, V> {
    type Output: OutputHolder<V>;

    fn new() -> Self;
    fn get(&self, key: &K) -> Option<Self::Output>;
    fn insert(&self, key: K, value: V) -> Result<(), Self::Output>;
    fn remove(&self, key: &K) -> Option<Self::Output>;
}

#[cfg(test)]
pub mod tests {
    extern crate rand;
    use super::{ConcurrentMap, OutputHolder};
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    pub fn smoke<M: ConcurrentMap<i32, String> + Send + Sync>() {
        let map = &M::new();

        thread::scope(|s| {
            for t in 0..THREADS {
                s.spawn(move |_| {
                    let rng = &mut rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(rng);
                    for i in keys {
                        assert!(map.insert(i, i.to_string()).is_ok());
                    }
                });
            }
        })
        .unwrap();

        thread::scope(|s| {
            for t in 0..(THREADS / 2) {
                s.spawn(move |_| {
                    let rng = &mut rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(rng);
                    for i in keys {
                        assert_eq!(i.to_string(), *map.remove(&i).as_ref().unwrap().output());
                    }
                });
            }
        })
        .unwrap();

        thread::scope(|s| {
            for t in (THREADS / 2)..THREADS {
                s.spawn(move |_| {
                    let rng = &mut rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(rng);
                    for i in keys {
                        assert_eq!(i.to_string(), *map.get(&i).as_ref().unwrap().output());
                    }
                });
            }
        })
        .unwrap();
    }
}
