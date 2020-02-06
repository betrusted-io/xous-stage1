#![no_std]
#![no_main]

use core::{mem, ptr};

pub type XousPid = u8;
const PAGE_SIZE: u32 = 4096;
const MAX_PROCESS_COUNT: usize = 256;

struct BootConfig {
    /// `true` if the kernel and Init programs run XIP
    no_copy: bool,

    /// Base load address.  Defaults to the start of the args block
    base_addr: *const u32,

    /// The size of the kernel args tagged data
    args_size: u32,

    /// The start of the memory region listing
    regions_start: *mut u32,

    /// The size of the memory region listing, in bytes
    regions_size: u32,

    sram_start: *mut u32,
    sram_size: u32,

    /// Total number of bytes required for kernel + init images.
    /// NOTE: If `no_copy` is `true` then this value is ignored.
    /// NOTE: Each process is rounded off to the nearest page.
    /// That is, if both the kernel and one init process each
    /// require 3000 bytes, this value is (4096 + 4096) = 8192.
    init_size: u32,
}

/// A single RISC-V page table entry.  In order to resolve an address,
/// we need two entries: the top level, followed by the lower level.
struct PageTable {
    entries: [u32; 1024],
}

struct Process {
    /// The MMU address.  If the high bit is not set, then it is not valid.
    satp: u32,

    /// Where this process is in terms of lifecycle
    state: u32,

    /// The last address of the program counter
    pc: u32,
}

struct ProcessTable {
    processes: [Process; MAX_PROCESS_COUNT],
}

/// This describes both the kernel and PID1
struct ProgramDescription {
    /// Physical source address of this program in RAM (i.e. SPI flash)
    load_offset: u32,

    /// How many bytes of data to load from the source to the target
    load_size: u32,

    /// Start of the virtual address where the .text section will go.
    /// This section will be marked non-writable, executable.
    text_offset: u32,

    /// Start of the virtual address of .data and .bss section in RAM.
    /// This will simply allocate this memory and mark it "read-write"
    /// without actually copying any data.
    data_offset: u32,

    /// Size of .data and .bss section.  This many bytes will be allocated
    /// for the data section.
    data_size: u32,

    /// Virtual address entry point.
    entrypoint: u32,

    /// Virtual address of the top of the stack pointer.  This process will
    /// get one page allocated.  Additional pages will be allocated as stack
    /// grows and faults occur.
    stack_offset: u32,
}

struct Allocator {
    next_page_offset: u32,
    runtime_page_tracker: *mut XousPid,
    sram_start: *mut u8,
}

impl ProgramDescription {
    pub fn load(&self, allocator: &mut Allocator, processes: &mut ProcessTable) -> u32 {
        // Not a great algorithm!
        for i in 0..processes.processes.len() as u32 {
            if processes.processes[i as usize].satp & 0x80000000 != 0 {
                continue;
            }
            let sp_page = allocator.alloc() as u32;

            let satp = allocator.alloc() as u32;
            unsafe { set_satp((satp >> 10) | 0x80000000 | ((i + 1) << 22)) };
            processes.processes[i as usize].satp = satp;
            let satp = unsafe { &mut *(satp as *mut PageTable) };

            allocator.map_page(satp, sp_page, self.stack_offset);
            assert!((self.load_offset & (PAGE_SIZE - 1)) == 0);
            assert!((self.data_offset & (PAGE_SIZE - 1)) == 0);
            for offset in (0..self.load_size).step_by(PAGE_SIZE as usize) {
                let page_addr = allocator.alloc();
                allocator.map_page(satp, page_addr as u32, self.text_offset + offset);
                let mut to_copy = PAGE_SIZE;
                if self.load_size - offset < to_copy {
                    to_copy = self.load_size - offset;
                }
                unsafe {
                    memcpy(
                        page_addr,
                        (self.load_offset + offset) as *mut u32,
                        to_copy as usize,
                    )
                };
            }

            for offset in (0..self.data_size).step_by(PAGE_SIZE as usize) {
                let page_addr = allocator.alloc();
                allocator.map_page(satp, page_addr as u32, self.data_offset + offset);
            }
            processes.processes[i as usize].pc = self.entrypoint;
            processes.processes[i as usize].state = 1;

            return self.entrypoint;
        }
        panic!("no free process found");
    }
}

macro_rules! make_type {
    ($fcc:expr) => {{
        let mut c: [u8; 4] = Default::default();
        c.copy_from_slice($fcc.as_bytes());
        u32::from_le_bytes(c)
    }};
}

extern "C" {
    /// Set the stack pointer to the given address.
    fn set_sp(sp: u32);

    // Enable the MMU with the given translation pointer
    fn set_satp(satp: u32);

// fn start_kernel(entrypoint: u32, args: u32, )
}

pub unsafe fn bzero<T>(mut sbss: *mut T, ebss: *mut T)
where
    T: Copy,
{
    while sbss < ebss {
        // NOTE(volatile) to prevent this from being transformed into `memclr`
        ptr::write_volatile(sbss, mem::zeroed());
        sbss = sbss.offset(1);
    }
}

pub unsafe fn memcpy<T>(dest: *mut T, src: *const T, count: usize)
where
    T: Copy,
{
    let mut offset = 0;
    while offset < (count / mem::size_of::<T>()) {
        dest.add(offset)
            .write_volatile(src.add(offset).read_volatile());
        offset = offset + 1;
    }
}

use core::panic::PanicInfo;
#[panic_handler]
fn handle_panic(_arg: &PanicInfo) -> ! {
    loop {}
}

fn read_next_tag(b8: *const u8, byte_offset: &mut usize) -> Result<(u32, u32, u32), ()> {
    let tag_name = u32::from_le(unsafe { (b8 as *mut u32).add(*byte_offset / 4).read() }) as u32;
    *byte_offset += 4;
    let crc = u16::from_le(unsafe { (b8 as *mut u16).add(*byte_offset / 2).read() }) as u32;
    *byte_offset += 2;
    let size = u16::from_le(unsafe { (b8 as *mut u16).add(*byte_offset / 2).read() }) as u32 * 4;
    *byte_offset += 2;
    Ok((tag_name, crc, size))
}

fn read_initial_config(b8: *const u8, cfg: &mut BootConfig) {
    let mut byte_offset = 0;

    let (tag_name, _crc, size) =
        read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
    if tag_name != make_type!("XASZ") || size != 4 {
        panic!("XASZ wasn't first tag, or was invalid size");
    }
    let total_bytes = unsafe { (b8 as *const usize).add(byte_offset / 4).read() } * 4;
    byte_offset += 4;
    cfg.args_size = total_bytes as u32;

    while byte_offset < total_bytes {
        let (tag_name, _crc, size) =
            read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
        if tag_name == make_type!("MBLK") {
            cfg.regions_start = unsafe { b8.add(byte_offset) as *mut u32 };
            cfg.regions_size = size;
            cfg.sram_start = unsafe { (b8.add(byte_offset + 4) as *mut u32).read() } as *mut u32;
            cfg.sram_size = unsafe { (b8.add(byte_offset + 8) as *mut u32).read() };
        } else if tag_name == make_type!("Bflg") {
            let boot_flags = unsafe { (b8.add(byte_offset) as *mut u32).read() };
            if boot_flags & 1 != 0 {
                cfg.no_copy = true;
            }
            if boot_flags & 2 != 0 {
                cfg.base_addr = 0 as *mut u32;
            }
        } else if tag_name == make_type!("XKRN") || tag_name == make_type!("Init") {
            let load_size = unsafe { (b8.add(byte_offset) as *mut u32).add(1).read() };
            cfg.init_size = (load_size + 4096 - 1) & !(4096 - 1);
        }
        byte_offset += size as usize;
    }

    if byte_offset > total_bytes {
        panic!(
            "exceeded total bytes ({}) with byte_offset of {}",
            total_bytes, byte_offset
        );
    }
}

fn copy_processes(cfg: &mut BootConfig, args: *const u8) {
    let mut byte_offset = 0;
    let mut top = cfg.get_top();

    while byte_offset < cfg.args_size as usize {
        let (tag_name, _crc, size) =
            read_next_tag(args, &mut byte_offset).expect("couldn't read next tag");
        if tag_name == make_type!("XKRN") || tag_name == make_type!("Init") {
            let load_offset = unsafe { (args.add(byte_offset) as *mut u32).add(0).read() };
            let load_size = unsafe { (args.add(byte_offset) as *mut u32).add(1).read() };

            // Round it off to a page boundary
            let load_size_rounded = (load_size + 4096 - 1) & !(4096 - 1);
            cfg.init_size += load_size_rounded;
            top = unsafe { top.sub(load_size_rounded as usize) };
            let base = unsafe { cfg.base_addr.add(load_offset as usize / 4) };
            unsafe { memcpy(top, base, load_size as usize) };
            unsafe {
                bzero(
                    top.add(load_size as usize / 4),
                    top.add(load_size_rounded as usize / 4),
                )
            };
        }
        byte_offset += size as usize;
    }

    if byte_offset > cfg.args_size as usize {
        panic!(
            "exceeded total bytes ({}) with byte_offset of {}",
            cfg.args_size, byte_offset
        );
    }
}

/// Stage 1 Bootloader
/// This makes the program self-sufficient by setting up memory page assignment
/// and copying the arguments to RAM
#[export_name = "stage1"]
pub unsafe extern "C" fn early_init(arg_buffer: *const u8, signature: u32) -> ! {
    stage1(arg_buffer, signature);
}

impl BootConfig {
    fn get_top(&self) -> *mut u32 {
        unsafe {
            self.sram_start
                .add((self.sram_size - self.init_size) as usize / 4)
        }
    }
}

/// Allocate and initialize memory regions.
/// Returns a pointer to the start of the memory region.
fn allocate_regions(cfg: &mut BootConfig) -> (*mut u32, u32) {
    let top = cfg.get_top();
    // Number of individual pages in the system
    let mut runtime_page_tracker_len = 0;
    for region_offset in (0..(cfg.regions_size / 4) as usize).step_by(3) {
        // let _region_start = cfg.regions_start.add(region_offset + 0).read();
        let region_length = unsafe { cfg.regions_start.add(region_offset + 1).read() };
        // let _region_name = cfg.regions_start.add(region_offset + 2).read();
        runtime_page_tracker_len += region_length * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;
    }

    // Clear all memory pages such that they're not owned by anyone
    let runtime_page_tracker = unsafe { top.sub(runtime_page_tracker_len as usize / 4) };
    unsafe {
        bzero(
            runtime_page_tracker,
            runtime_page_tracker.add((runtime_page_tracker_len / 4) as usize),
        );
    }

    cfg.init_size += runtime_page_tracker_len;

    (runtime_page_tracker, runtime_page_tracker_len)
}

fn allocate_processes(cfg: &mut BootConfig) -> (*mut u32, u32) {
    let top = cfg.get_top();
    // Allocate the process table
    let runtime_process_table_len = mem::size_of::<ProcessTable>() as u32;
    let runtime_process_table = unsafe { top.sub(runtime_process_table_len as usize / 4) };
    unsafe {
        bzero(
            runtime_process_table,
            runtime_process_table.add((runtime_process_table_len / 4) as usize),
        );
    }

    cfg.init_size += runtime_process_table_len;

    (runtime_process_table, runtime_process_table_len)
}

fn copy_args(cfg: &mut BootConfig, arg_buffer: *const u8, top: *mut u32) -> *const u8 {
    // Copy the args list to target RAM
    let runtime_arg_buffer = unsafe { top.sub(cfg.args_size as usize / 4) };
    unsafe {
        memcpy(
            runtime_arg_buffer,
            arg_buffer as *mut u32,
            cfg.args_size as usize,
        )
    };
    cfg.init_size += cfg.args_size;

    runtime_arg_buffer as *const u8
}

fn stage1(mut arg_buffer: *const u8, _signature: u32) -> ! {
    let mut cfg = BootConfig {
        no_copy: false,
        base_addr: arg_buffer as *const u32,
        regions_start: 0 as *mut u32,
        regions_size: 0,
        sram_start: 0 as *mut u32,
        sram_size: 0,
        args_size: 0,
        init_size: 0,
    };
    read_initial_config(arg_buffer, &mut cfg);
    let sram_end = unsafe { cfg.sram_start.add(cfg.sram_size as usize / 4) };

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    let (runtime_page_tracker, runtime_page_tracker_len) = allocate_regions(&mut cfg);

    // Processes are also stored in RAM
    let (runtime_process_table, runtime_process_table_len) =
        allocate_processes(&mut cfg);

    // Copy the arguments, if requested
    if !cfg.no_copy {
        arg_buffer = copy_args(&mut cfg, arg_buffer, runtime_process_table);
    }

    // All further allocations must be page-aligned.
    cfg.init_size = (cfg.init_size + 4096 - 1) & !(4096 - 1);

    // Allocate a stack pointer
    // Up until now we've been using the stack pointer from the bootloader.
    // Allocate us a stack pointer directly below the memory page tracker,
    // and enable it.
    let sp = unsafe { cfg.get_top().sub(1) };
    unsafe { set_sp(sp as u32) };
    cfg.init_size = (cfg.init_size + 4096 - 1) & !(4096 - 1);

    if !cfg.no_copy {
        copy_processes(&mut cfg, arg_buffer);
    }

    // Mark all pages as in-use by the kernel
    for i in 0..(cfg.init_size / PAGE_SIZE) {
        unsafe {
            (runtime_page_tracker as *mut XousPid)
                .add((runtime_page_tracker_len - i - 1) as usize)
                .write_volatile(1)
        };
    }

    let mut runtime_process_table = unsafe { &mut *(runtime_process_table as *mut ProcessTable) };

    // // Drop write permissions for the arg buffer
    // let runtime_arg_buffer = runtime_arg_buffer as *const u8;

    // // Mark these pages as being owned by PID1.
    // // Add an extra page to store the stack pointer, also owned by PID1.
    // for offset in (sram_len - cfg.args_size - mem_page_byte_count - runtime_process_table_len - 4096) / PAGE_SIZE..(sram_len / PAGE_SIZE) {
    //     (runtime_page_tracker as *mut XousPid)
    //         .add(offset as usize)
    //         .write(1);
    // }

    // stage2(
    //     runtime_arg_buffer,
    //     cfg.args_size,
    //     runtime_page_tracker as *mut XousPid,
    //     mem_page_byte_count,
    //     &mut runtime_process_table,
    //     sram_start as *mut u8,
    //     sram_len,
    // );
    loop {}
}

impl Allocator {
    /// Zero-alloc a new page, mark it as owned by PID1, and return it.
    /// Decrement the `next_page_offset` (npo) variable by one page.
    pub fn alloc(&mut self) -> *mut u32 {
        self.next_page_offset = self.next_page_offset - PAGE_SIZE as u32;
        unsafe {
            // Grab the page address and zero it out
            let pg = self.sram_start.add(self.next_page_offset as usize);
            bzero(pg as *mut u32, pg.add(PAGE_SIZE as usize) as *mut u32);

            // Mark this page as in-use by PID1
            self.runtime_page_tracker
                .add((self.next_page_offset / PAGE_SIZE) as usize)
                .write_volatile(1);

            // Return the address
            pg as *mut u32
        }
    }

    /// Map the given page to the specified process table.  If necessary,
    /// allocate a new page.
    ///
    /// # Panics
    ///
    /// * If you try to map a page twice
    pub fn map_page(&mut self, root: &mut PageTable, phys: u32, virt: u32) {
        let ppn1 = (phys >> 22) & ((1 << 12) - 1);
        let ppn0 = (phys >> 12) & ((1 << 10) - 1);
        let ppo = (phys >> 0) & ((1 << 12) - 1);

        let vpn1 = (virt >> 22) & ((1 << 10) - 1);
        let vpn0 = (virt >> 12) & ((1 << 10) - 1);
        let vpo = (virt >> 0) & ((1 << 12) - 1);

        assert!(ppn1 < 4096);
        assert!(ppn0 < 1024);
        assert!(ppo < 4096);
        assert!(vpn1 < 1024);
        assert!(vpn0 < 1024);
        assert!(vpo < 4096);

        let ref mut l1_pt = root.entries;

        // Allocate a new level 1 pagetable entry if one doesn't exist.
        if l1_pt[vpn1 as usize] & 1 == 0 {
            let new_addr = self.alloc() as u32;

            // Mark this entry as a leaf node (WRX as 0), and indicate
            // it is a valid page by setting "V".
            let ppn = new_addr >> 12;
            l1_pt[vpn1 as usize] = (ppn << 10) | 1;
        }

        let l0_pt_idx =
            unsafe { &mut (*(((l1_pt[vpn1 as usize] << 2) & !((1 << 12) - 1)) as *mut PageTable)) };
        let ref mut l0_pt = l0_pt_idx.entries;

        // Ensure the entry hasn't already been mapped.
        if l0_pt[vpn0 as usize] & 1 != 0 {
            panic!("Page already allocated!");
        }
        l0_pt[vpn0 as usize] = (ppn1 << 20) | (ppn0 << 10) | 1 | 0xe | 0xd0;
    }
}

/// Stage 2 bootloader
/// This sets up the MMU and loads both PID1 and the kernel into RAM.
fn stage2(
    runtime_args: *const u8,
    runtime_args_len: u32,
    runtime_page_tracker: *mut XousPid,
    runtime_page_tracker_len: u32,
    runtime_process_table: &mut ProcessTable,
    sram_start: *mut u8,
    sram_len: u32,
) -> ! {
    // next page offset is in units of bytes.
    // The offset is from the start of SRAM.
    let next_page_offset =
        (sram_len - runtime_args_len - runtime_page_tracker_len - PAGE_SIZE) & !(PAGE_SIZE - 1);
    let sp_page = next_page_offset;

    let mut allocator = Allocator {
        next_page_offset,
        runtime_page_tracker,
        sram_start,
    };

    // Loop through the kernel args and copy the kernel and PID1
    let mut args_offset = 0;
    let mut xkrn_seen = false;
    let mut kernel_entrypoint = 0;
    while args_offset < runtime_args_len as usize {
        let (tag_name, _crc, size) =
            read_next_tag(runtime_args, &mut args_offset).expect("couldn't read next tag");
        if tag_name == make_type!("Init") {
            assert!(size == 28, "invalid Init size");
            let pid1 = unsafe { &*(runtime_args.add(args_offset) as *const ProgramDescription) };
            pid1.load(&mut allocator, runtime_process_table);
        }
        if tag_name == make_type!("XKRN") {
            assert!(size == 28, "invalid XKRN size");
            assert!(!xkrn_seen, "xkrn appears twice");
            let xkrn = unsafe { &*(runtime_args.add(args_offset) as *const ProgramDescription) };
            kernel_entrypoint = xkrn.load(&mut allocator, runtime_process_table);
            xkrn_seen = true;
        }
    }

    loop {}
}
