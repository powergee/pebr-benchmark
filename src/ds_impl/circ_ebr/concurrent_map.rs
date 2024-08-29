use circ::Guard;

pub trait OutputHolder<'g, V> {
    fn output(&self) -> &'g V;
}

pub trait ConcurrentMap<K, V> {
    type Output<'g>: OutputHolder<'g, V>;

    fn new() -> Self;
    fn get<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>>;
    fn insert<'g>(&self, key: K, value: V, cs: &'g Guard) -> bool;
    fn remove<'g>(&self, key: &K, cs: &'g Guard) -> Option<Self::Output<'g>>;
}

#[cfg(test)]
pub mod tests {
    extern crate rand;
    use super::{ConcurrentMap, OutputHolder};
    use circ::cs;
    use crossbeam_utils::thread;
    use rand::prelude::*;

    const THREADS: i32 = 30;
    const ELEMENTS_PER_THREADS: i32 = 1000;

    pub fn smoke<M: ConcurrentMap<i32, String> + Send + Sync>() {
        let map = &M::new();

        thread::scope(|s| {
            for t in 0..THREADS {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(&mut rng);
                    for i in keys {
                        assert!(map.insert(i, i.to_string(), &cs()));
                    }
                });
            }
        })
        .unwrap();

        thread::scope(|s| {
            for t in 0..(THREADS / 2) {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(&mut rng);
                    let cs = &mut cs();
                    for i in keys {
                        assert_eq!(i.to_string(), *map.remove(&i, cs).unwrap().output());
                        cs.reactivate();
                    }
                });
            }
        })
        .unwrap();

        thread::scope(|s| {
            for t in (THREADS / 2)..THREADS {
                s.spawn(move |_| {
                    let mut rng = rand::thread_rng();
                    let mut keys: Vec<i32> =
                        (0..ELEMENTS_PER_THREADS).map(|k| k * THREADS + t).collect();
                    keys.shuffle(&mut rng);
                    let cs = &mut cs();
                    for i in keys {
                        {
                            let result = map.get(&i, cs);
                            if (0..THREADS / 2).contains(&i) {
                                assert!(result.is_none());
                            } else {
                                assert_eq!(i.to_string(), *result.unwrap().output());
                            }
                        }
                        cs.reactivate();
                    }
                });
            }
        })
        .unwrap();
    }
}
