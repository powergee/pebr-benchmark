extern crate clap;
extern crate csv;

extern crate smr_benchmark;

use clap::{value_parser, Arg, ArgMatches, Command, ValueEnum};
use crossbeam_utils::thread::scope;
use csv::Writer;
use rand::distributions::Uniform;
use rand::prelude::*;
use smr_benchmark::ds_impl;
use std::cmp::max;
use std::fmt;
use std::fs::{create_dir_all, File, OpenOptions};
use std::io::{stdout, Write};
use std::path::Path;
use std::sync::{mpsc, Arc, Barrier};
use std::time::{Duration, Instant};
use typenum::{Unsigned, U1};

#[derive(PartialEq, Debug, ValueEnum, Clone)]
#[allow(non_camel_case_types)]
pub enum MM {
    NR,
}

pub enum OpsPerCs {
    One,
    Four,
}

impl fmt::Display for OpsPerCs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            OpsPerCs::One => write!(f, "1"),
            OpsPerCs::Four => write!(f, "4"),
        }
    }
}

struct Config {
    mm: MM,
    readers: usize,
    writers: usize,

    aux_thread: usize,
    aux_thread_period: Duration,
    sampling: bool,
    sampling_period: Duration,

    key_dist: Uniform<usize>,
    prefill: usize,
    interval: u64,
    duration: Duration,

    mem_sampler: MemSampler,
}

struct MemSampler {}
impl MemSampler {
    pub fn new() -> Self {
        println!("NOTE: Memory usage benchmark is supported only for linux.");
        MemSampler {}
    }
    pub fn sample(&self) -> usize {
        0
    }
}

fn main() {
    let matches = Command::new("smr_benchmark")
        .arg(
            Arg::new("memory manager")
                .short('m')
                .value_parser(value_parser!(MM))
                .required(true)
                .ignore_case(true)
                .help("Memeory manager(s)"),
        )
        .arg(
            Arg::new("writers")
                .short('w')
                .value_parser(value_parser!(usize))
                .required(true)
                .help("Numbers of threads which perform only write operations."),
        )
        .arg(
            Arg::new("readers")
                .short('g')
                .value_parser(value_parser!(usize))
                .required(true)
                .help("Numbers of threads which perform only get operations."),
        )
        .arg(
            Arg::new("range")
                .short('r')
                .value_parser(value_parser!(usize))
                .help("Key range: [0..RANGE]")
                .default_value("100000"),
        )
        .arg(
            Arg::new("interval")
                .short('i')
                .value_parser(value_parser!(u64))
                .help("Time interval in seconds to run the benchmark")
                .default_value("10"),
        )
        .arg(
            Arg::new("sampling period")
                .short('s')
                .value_parser(value_parser!(u64))
                .help(
                    "The period to query jemalloc stats.allocated (ms). 0 for no sampling. \
                     Only supported on linux.",
                )
                .default_value("1"),
        )
        .arg(
            Arg::new("output")
                .short('o')
                .help("Output CSV filename. Appends the data if the file already exists."),
        )
        .get_matches();

    let (config, mut output) = setup(matches);
    bench::<U1>(&config, output.as_mut());
}

fn setup(m: ArgMatches) -> (Config, Option<Writer<File>>) {
    let mm = m.get_one::<MM>("memory manager").cloned().unwrap();
    let writers = m.get_one::<usize>("writers").copied().unwrap();
    let readers = m.get_one::<usize>("readers").copied().unwrap();
    let range = m.get_one::<usize>("range").copied().unwrap();
    let prefill = range / 2;
    let key_dist = Uniform::from(0..range);
    let interval = m.get_one::<u64>("interval").copied().unwrap();
    let sampling_period = m.get_one::<u64>("sampling period").copied().unwrap();
    let sampling = sampling_period > 0 && cfg!(all(not(feature = "sanitize"), target_os = "linux"));
    let duration = Duration::from_secs(interval);

    assert!(
        readers >= 1,
        "The number of readers must be greater than zero!"
    );

    let output = m.get_one::<String>("output").map(|output_name| {
        let output_path = Path::new(output_name);
        let dir = output_path.parent().unwrap();
        create_dir_all(dir).unwrap();
        match OpenOptions::new()
            .read(true)
            .write(true)
            .append(true)
            .open(&output_name)
        {
            Ok(f) => csv::Writer::from_writer(f),
            Err(_) => {
                let f = OpenOptions::new()
                    .read(true)
                    .write(true)
                    .create(true)
                    .open(&output_name)
                    .unwrap();
                let mut output = csv::Writer::from_writer(f);
                // NOTE: `write_record` on `bench`
                output
                    .write_record(&[
                        "mm",
                        "sampling_period",
                        "throughput",
                        "peak_mem",
                        "avg_mem",
                        "peak_garb",
                        "avg_garb",
                        "key_range",
                    ])
                    .unwrap();
                output.flush().unwrap();
                output
            }
        }
    });
    let mem_sampler = MemSampler::new();
    let config = Config {
        mm,
        writers,
        readers,

        aux_thread: if sampling { 1 } else { 0 },
        aux_thread_period: Duration::from_millis(1),
        sampling,
        sampling_period: Duration::from_millis(sampling_period),

        key_dist,
        prefill,
        interval,
        duration,

        mem_sampler,
    };
    (config, output)
}

fn bench<N: Unsigned>(config: &Config, output: Option<&mut Writer<File>>) {
    println!(
        "{}: {} writers, {} readers",
        config.mm.to_possible_value().unwrap().get_name(),
        config.writers,
        config.readers
    );
    let (ops_per_sec, peak_mem, avg_mem, peak_garb, avg_garb) = match config.mm {
        MM::NR => bench_map_nr(config, PrefillStrategy::Decreasing),
    };
    if let Some(output) = output {
        output
            .write_record(&[
                config
                    .mm
                    .to_possible_value()
                    .unwrap()
                    .get_name()
                    .to_string(),
                config.sampling_period.as_millis().to_string(),
                ops_per_sec.to_string(),
                peak_mem.to_string(),
                avg_mem.to_string(),
                peak_garb.to_string(),
                avg_garb.to_string(),
                (config.prefill * 2).to_string(),
            ])
            .unwrap();
        output.flush().unwrap();
    }
    println!(
        "ops/s: {}, peak mem: {}, avg_mem: {}, peak garb: {}, avg garb: {}",
        ops_per_sec, peak_mem, avg_mem, peak_garb, avg_garb
    );
}

#[allow(unused)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrefillStrategy {
    Random,
    Decreasing,
}

impl PrefillStrategy {
    fn prefill_ebr<M: ds_impl::nr::ConcurrentMap<usize, usize> + Send + Sync>(
        self,
        config: &Config,
        map: &M,
    ) {
        let rng = &mut rand::thread_rng();
        match self {
            PrefillStrategy::Random => {
                for _ in 0..config.prefill {
                    let key = config.key_dist.sample(rng);
                    let value = key;
                    map.insert(key, value);
                }
            }
            PrefillStrategy::Decreasing => {
                let mut keys = Vec::with_capacity(config.prefill);
                for _ in 0..config.prefill {
                    keys.push(config.key_dist.sample(rng));
                }
                keys.sort_by(|a, b| b.cmp(a));
                for key in keys.drain(..) {
                    let value = key;
                    map.insert(key, value);
                }
            }
        }
        print!("prefilled... ");
        stdout().flush().unwrap();
    }
}

fn bench_map_nr(config: &Config, strategy: PrefillStrategy) -> (u64, usize, usize, usize, usize) {
    use ds_impl::nr::ConcurrentMap;
    let map = &ds_impl::nr::HHSList::new();
    strategy.prefill_ebr(config, map);

    let barrier = &Arc::new(Barrier::new(
        config.writers + config.readers + config.aux_thread,
    ));
    let (ops_sender, ops_receiver) = mpsc::channel();
    let (mem_sender, mem_receiver) = mpsc::channel();

    scope(|s| {
        if config.aux_thread > 0 {
            let mem_sender = mem_sender.clone();
            s.spawn(move |_| {
                assert!(config.sampling);
                let mut samples = 0usize;
                let mut acc = 0usize;
                let mut peak = 0usize;
                let mut _garb_acc = 0usize;
                let mut _garb_peak = 0usize;
                barrier.clone().wait();

                let start = Instant::now();
                let mut next_sampling = start + config.sampling_period;
                while start.elapsed() < config.duration {
                    let now = Instant::now();
                    if now > next_sampling {
                        let allocated = config.mem_sampler.sample();
                        samples += 1;

                        acc += allocated;
                        peak = max(peak, allocated);

                        next_sampling = now + config.sampling_period;
                    }
                    std::thread::sleep(config.aux_thread_period);
                }
                mem_sender
                    .send((peak, acc / samples, _garb_peak, _garb_acc / samples))
                    .unwrap();
            });
        } else {
            mem_sender.send((0, 0, 0, 0)).unwrap();
        }

        // Spawn writer threads.
        for _ in 0..config.writers {
            s.spawn(move |_| {
                barrier.clone().wait();
                let start = Instant::now();

                let mut acquired = None;
                while start.elapsed() < config.duration {
                    if let Some((key, value)) = acquired.take() {
                        assert!(map.insert(key, value));
                    } else {
                        let (key, value) = map.pop().unwrap();
                        acquired = Some((key.clone(), value.clone()));
                    }
                }
            });
        }

        // Spawn reader threads.
        for _ in 0..config.readers {
            let ops_sender = ops_sender.clone();
            s.spawn(move |_| {
                let mut ops: u64 = 0;
                let rng = &mut rand::thread_rng();
                barrier.clone().wait();
                let start = Instant::now();

                while start.elapsed() < config.duration {
                    let key = config.key_dist.sample(rng);
                    let _ = map.get(&key);
                    ops += 1;
                }

                ops_sender.send(ops).unwrap();
            });
        }
    })
    .unwrap();
    println!("end");

    let mut ops = 0;
    for _ in 0..config.readers {
        let local_ops = ops_receiver.recv().unwrap();
        ops += local_ops;
    }
    let ops_per_sec = ops / config.interval;
    let (peak_mem, avg_mem, garb_peak, garb_avg) = mem_receiver.recv().unwrap();
    (ops_per_sec, peak_mem, avg_mem, garb_peak, garb_avg)
}
