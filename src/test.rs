use lazy_static::lazy_static;

use std::sync::Mutex;

fn get_args_bin() -> &'static [u8] {
    include_bytes!("../test/args.bin")
}

const REGION_COUNT: usize = 8;
static mut MEMORY_REGIONS: [[usize; 1024 * 1024]; REGION_COUNT] = [[0usize; 1024 * 1024]; REGION_COUNT];
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

#[test]
fn copy_processes() {
    use crate::args::KernelArguments;
    use crate::BootConfig;

    // Create a fake memory block into which the bootloader will write
    let fake_memory = FakeMemory::get();

    let args = get_args_bin();
    let ka = KernelArguments::new(args.as_ptr() as *const usize);
    let mut cfg = BootConfig {
        args_base: ka.base as *const usize,
        base_addr: ka.base as *const usize,
        ..Default::default()
    };
    crate::read_initial_config(&mut cfg, &ka);

    // Patch up the config memory address
    cfg.sram_start = fake_memory.region.as_ptr() as *mut _;
    cfg.sram_size = fake_memory.region.len() / core::mem::size_of::<usize>();
    crate::copy_processes(&mut cfg, &ka);
}

#[test]
fn allocate_regions() {
    use crate::args::KernelArguments;
    use crate::BootConfig;

    // Create a fake memory block into which the bootloader will write
    let fake_memory = FakeMemory::get();

    let args = get_args_bin();
    let ka = KernelArguments::new(args.as_ptr() as *const usize);
    let mut cfg = BootConfig {
        args_base: ka.base as *const usize,
        base_addr: ka.base as *const usize,
        ..Default::default()
    };
    crate::read_initial_config(&mut cfg, &ka);

    // Patch up the config memory address
    cfg.sram_start = fake_memory.region.as_ptr() as *mut _;
    cfg.sram_size = fake_memory.region.len() / core::mem::size_of::<usize>();

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    crate::allocate_regions(&mut cfg);

    // The kernel, as well as initial processes, are all stored in RAM.
    crate::allocate_processes(&mut cfg);
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

    // Create a fake memory block into which the bootloader will write
    // let mut fake_memory = [0usize; 1024 * 128];

    let args = get_args_bin();
    let ka = KernelArguments::new(args.as_ptr() as *const usize);
    let mut cfg = BootConfig {
        args_base: ka.base as *const usize,
        ..Default::default()
    };
    crate::read_initial_config(&mut cfg, &ka);
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
    loop {};
}
