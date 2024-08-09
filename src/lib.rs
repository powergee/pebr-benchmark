#![doc = include_str!("../README.md")]
#![feature(strict_provenance_atomic_ptr, strict_provenance)]
#![feature(cfg_sanitize)]

#[allow(unused_imports)]
#[macro_use]
extern crate cfg_if;

pub struct MemSampler {}

impl Default for MemSampler {
    fn default() -> Self {
        Self::new()
    }
}

impl MemSampler {
    pub fn new() -> Self {
        println!("NOTE: Memory usage benchmark is supported only for linux.");
        MemSampler {}
    }
    pub fn sample(&self) -> usize {
        0
    }
}

extern crate crossbeam_utils;
#[macro_use]
extern crate bitflags;
extern crate clap;
extern crate typenum;

#[macro_use]
mod utils;
pub mod config;
pub mod ds_impl;
