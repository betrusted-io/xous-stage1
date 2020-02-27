use lazy_static::lazy_static;

use crate::BootConfig;
use std::sync::Mutex;

fn get_args_bin() -> &'static [u8] {
    include_bytes!("../test/args.bin")
}

const REGION_COUNT: usize = 8;
static mut MEMORY_REGIONS: [[usize; 1024 * 1024]; REGION_COUNT] =
    [[0usize; 1024 * 1024]; REGION_COUNT];
lazy_static! {
    static ref REGIONS_CHECKED_OUT: Mutex<[bool; REGION_COUNT]> = Mutex::new([false; REGION_COUNT]);
}

struct FakeMemory {
    pub region: &'static mut [usize; 1024 * 1024],
    index: usize,
}

impl FakeMemory {
    pub fn get() -> Self {
        unsafe {
            let mut store = REGIONS_CHECKED_OUT.lock().unwrap();
            let mut found_idx = None;
            for (idx, flag) in store.iter().enumerate() {
                if !flag {
                    found_idx = Some(idx);
                    break;
                }
            }
            let found_idx = found_idx.expect("no available memory regions found");
            println!("Checking out region {}", found_idx);
            store[found_idx] = true;
            FakeMemory {
                region: &mut MEMORY_REGIONS[found_idx],
                index: found_idx,
            }
        }
    }
}

impl Drop for FakeMemory {
    fn drop(&mut self) {
        println!("Checking region {} back in", self.index);
        match REGIONS_CHECKED_OUT.lock() {
            Ok(mut o) => o[self.index] = false,
            Err(e) => println!("not checking in because of a panic: {:?}", e),
        }
    }
}

struct TestEnvironment {
    pub cfg: BootConfig,
    _mem: FakeMemory,
}

impl TestEnvironment {
    pub fn new() -> TestEnvironment {
        use crate::args::KernelArguments;

        // Create a fake memory block into which the bootloader will write
        let fake_memory = FakeMemory::get();
        // use rand::prelude::*;
        // for mem in fake_memory.region.iter_mut() {
        //     *mem = random();
        // }

        let args = get_args_bin();
        let ka = KernelArguments::new(args.as_ptr() as *const usize);
        let mut cfg = BootConfig {
            args: ka,
            base_addr: ka.base as *const usize,
            ..Default::default()
        };
        crate::read_initial_config(&mut cfg);

        // Patch up the config memory address.  Ensure the range is on a "page" boundary.
        let raw_ptr = fake_memory.region.as_mut_ptr() as usize;
        let raw_ptr_rounded = (raw_ptr + crate::PAGE_SIZE - 1) & !(crate::PAGE_SIZE - 1);

        cfg.sram_start = raw_ptr_rounded as *mut _;
        cfg.sram_size = fake_memory.region.len() * core::mem::size_of::<usize>() - crate::PAGE_SIZE;

        println!(
            "Patching RAM so it starts at {:016x} and is {} bytes long",
            fake_memory.region.as_ptr() as usize,
            fake_memory.region.len() * core::mem::size_of::<usize>()
        );

        TestEnvironment {
            cfg,
            _mem: fake_memory,
        }
    }
}

#[test]
fn copy_processes() {
    let mut env = TestEnvironment::new();
    crate::copy_processes(&mut env.cfg);
}

#[test]
fn allocate_regions() {
    let mut env = TestEnvironment::new();
    crate::copy_processes(&mut env.cfg);

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    println!("Allocating regions");
    crate::allocate_regions(&mut env.cfg);

    // The kernel, as well as initial processes, are all stored in RAM.
    println!("Allocating processes");
    crate::allocate_processes(&mut env.cfg);
}

#[test]
fn parse_args_bin() {
    use crate::args::KernelArguments;
    let args = get_args_bin();
    let ka = KernelArguments::new(args.as_ptr() as *const usize);

    let mut ka_iter = ka.iter();
    let ka_first = ka_iter.next().expect("kernel args has no first tag");
    assert_eq!(ka_first.name, make_type!("XArg"), "first tag was not valid");
    assert_eq!(ka_first.size, 20, "first tag had invalid size");
    assert_eq!(ka_first.data[1], 1, "tag version number unexpected");

    for arg in ka_iter {
        let tag_name_bytes = arg.name.to_le_bytes();
        let s = unsafe {
            use core::slice;
            use core::str;
            // First, we build a &[u8]...
            let slice = slice::from_raw_parts(tag_name_bytes.as_ptr(), 4);
            // ... and then convert that slice into a string slice
            str::from_utf8(slice).expect("tag had invalid utf8 characters")
        };

        println!("{} ({:08x}, {} bytes):", s, arg.name, arg.size);
        for word in arg.data {
            println!(" {:08x}", word);
        }
    }
}

#[test]
fn read_initial_config() {
    use crate::args::KernelArguments;
    use crate::BootConfig;

    let args = get_args_bin();
    let ka = KernelArguments::new(args.as_ptr() as *const usize);
    let mut cfg = BootConfig {
        args: ka,
        base_addr: ka.base as *const usize,
        ..Default::default()
    };
    crate::read_initial_config(&mut cfg);
}

#[test]
fn full_boot() {
    let mut env = TestEnvironment::new();

    println!("Running phase_1");
    crate::phase_1(&mut env.cfg);
    println!("Running phase_2");
    crate::phase_2(&mut env.cfg);
    println!("Done with phases");
}

#[test]
fn tracker_sane() {
    let mut env = TestEnvironment::new();

    crate::phase_1(&mut env.cfg);
    crate::phase_2(&mut env.cfg);

    let mut max_pid = 0;
    for process in env.cfg.processes.iter() {
        let satp = process.satp;
        let pid = (satp >> 22 & ((1<<9) - 1)) as u8;
        if pid > max_pid {
            max_pid = pid;
        }
        let mem_base = satp << 12;
        println!("Process {} @ {:08x} ({:08x}), entrypoint {:08x}, sp {:08x}", pid, mem_base, satp, process.entrypoint, process.sp);
    }

    for (idx, addr) in env.cfg.runtime_page_tracker.iter().enumerate() {
        assert!(*addr <= max_pid, "runtime page tracker contains invalid values @ {} ({:08x})! {} > {}", idx, addr as *const u8 as usize, *addr, max_pid);
    }
}

// Create a fake "start_kernel" function to allow
// this module to compile when not running natively.
#[export_name = "start_kernel"]
pub unsafe extern "C" fn start_kernel(
    _args: usize,
    _ss: usize,
    _rpt: usize,
    _satp: usize,
    _entrypoint: usize,
    _stack: usize,
) -> ! {
    loop {}
}
