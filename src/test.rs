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

fn read_word(satp: usize, virt: usize) -> Result<u32, &'static str> {
    if satp & 0x80000000 != 0x80000000 {
        return Err("satp valid bit isn't set");
    }
    // let ppn1 = (phys >> 22) & ((1 << 12) - 1);
    // let ppn0 = (phys >> 12) & ((1 << 10) - 1);
    // let ppo = (phys >> 0) & ((1 << 12) - 1);

    let vpn1 = (virt >> 22) & ((1 << 10) - 1);
    let vpn0 = (virt >> 12) & ((1 << 10) - 1);
    let vpo = (virt >> 0) & ((1 << 12) - 1);

    let l1_pt = unsafe { &mut (*((satp << 12) as *mut crate::PageTable)) };
    let l1_entry = l1_pt.entries[vpn1];
    // FIXME: This could also be a megapage
    if l1_entry & 7 != 1 {
        return Err("l1 page table not mapped");
    }
    let l0_pt = unsafe { &mut (*(((l1_entry >> 10) << 12) as *mut crate::PageTable)) };
    let l0_entry = l0_pt.entries[vpn0];
    if l0_entry & 1 != 1 {
        return Err("l0 page table not mapped");
    }
    // println!("l0_entry: {:08x}", l0_entry);
    let page_base = (((l0_entry as u32) >> 10) << 12) + vpo as u32;
    // println!("virt {:08x} -> phys {:08x}", virt, page_base);
    Ok(unsafe { (page_base as *mut u32).read() })
}

#[test]
fn full_boot() {
    let mut env = TestEnvironment::new();

    println!("Running phase_1");
    crate::phase_1(&mut env.cfg);
    println!("Running phase_2");
    crate::phase_2(&mut env.cfg);
    println!("Done with phases");

    let mut xkrn_inspected = false;
    for arg in env.cfg.args.iter() {
        if arg.name == make_type!("XKrn") {
            let prog = unsafe { &*(arg.data.as_ptr() as *const crate::ProgramDescription) };
            let program_offset = prog.load_offset as usize;
            let mut src_kernel = vec![];
            {
                let src_ptr = arg.data;
                for i in (0..(prog.load_size as usize)) {
                    let word = unsafe {
                        (env.cfg.base_addr as *mut u32)
                            .add((program_offset + i) / 4)
                            .read()
                    };
                    src_kernel.push(word);
                }
            }
            println!(
                "SATP @ {:08x}  Entrypoint @ {:08x}  Kernel: {} bytes starting from {:08x}",
                env.cfg.processes[0].satp as usize,
                env.cfg.processes[0].entrypoint as usize,
                src_kernel.len() * 4,
                prog.load_offset
            );
            for addr in (0..(prog.load_size as usize)).step_by(4) {
                assert_eq!(
                    src_kernel[addr],
                    read_word(env.cfg.processes[0].satp as usize, addr + 0x00200000).unwrap(),
                    "kernel doesn't match @ offset {:08x}",
                    addr + 0x00200000
                );
            }
            xkrn_inspected = true;
        }
    }
    assert_eq!(xkrn_inspected, true, "didn't see kernel in output list");
}

#[test]
fn tracker_sane() {
    let mut env = TestEnvironment::new();

    crate::phase_1(&mut env.cfg);
    crate::phase_2(&mut env.cfg);

    let mut max_pid = 0;
    for process in env.cfg.processes.iter() {
        let satp = process.satp;
        let pid = (satp >> 22 & ((1 << 9) - 1)) as u8;
        if pid > max_pid {
            max_pid = pid;
        }
        let mem_base = satp << 12;
        println!(
            "Process {} @ {:08x} ({:08x}), entrypoint {:08x}, sp {:08x}",
            pid, mem_base, satp, process.entrypoint, process.sp
        );
    }

    for (idx, addr) in env.cfg.runtime_page_tracker.iter().enumerate() {
        assert!(
            *addr <= max_pid,
            "runtime page tracker contains invalid values @ {} ({:08x})! {} > {}",
            idx,
            addr as *const u8 as usize,
            *addr,
            max_pid
        );
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
