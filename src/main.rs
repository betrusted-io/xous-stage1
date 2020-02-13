#![no_std]
#![no_main]

use core::{mem, ptr};

pub type XousPid = u8;
const PAGE_SIZE: u32 = 4096;
const MAX_PROCESS_COUNT: usize = 256;

const FLG_VALID: u32 = 0x1;
const FLG_X: u32 = 0x4;
const FLG_W: u32 = 0x4;
const FLG_R: u32 = 0x2;
const FLG_U: u32 = 0x10;
const FLG_A: u32 = 0x40;
const FLG_D: u32 = 0x80;

use core::panic::PanicInfo;
#[panic_handler]
fn handle_panic(_arg: &PanicInfo) -> ! {
    loop {}
}

/// Convert a four-letter string into a 32-bit int.
macro_rules! make_type {
    ($fcc:expr) => {{
        let mut c: [u8; 4] = Default::default();
        c.copy_from_slice($fcc.as_bytes());
        u32::from_le_bytes(c)
    }};
}

/// In-memory copy of the configuration page,
/// used by the stage-1 bootloader.
struct BootConfig {
    /// `true` if the kernel and Init programs run XIP
    no_copy: bool,

    /// Base load address.  Defaults to the start of the args block
    base_addr: *const u32,

    /// Where the tagged args lsit starts in RAM.
    args_start: *const u8,

    /// The size of the kernel args tagged data
    args_size: u32,

    /// The start of the memory region listing
    regions_start: *mut u32,

    /// The size of the memory region listing, in bytes
    regions_size: u32,

    /// The origin of usable memory.  This is where heap lives.
    sram_start: *mut u32,

    /// The size (in bytes) of the heap.
    sram_size: u32,

    /// A running total of the number of bytes consumed during
    /// initialization.  This value, divided by PAGE_SIZE,
    /// indicates the number of pages at the end of RAM that
    /// will need to be owned by PID1.
    init_size: u32,

    /// This structure keeps track of which pages are owned
    /// and which are free. A PID of `0` indicates it's free.
    runtime_page_tracker: *mut XousPid,

    /// The size (in bytes) of the `runtime_page_tracker`.
    runtime_page_tracker_len: u32,

    /// A list of system services.  Effectively, this contains
    /// the process table.
    system_services: *mut SystemServices,

    /// If `no_copy` is not set, this is the offset of the first
    /// page allocated to processes.
    process_offset: u32,
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

struct SystemServices {
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

extern "C" {
    /// Set the stack pointer to the given address.
    fn set_sp(sp: u32);

// fn start_kernel(entrypoint: u32, args: u32, )
}

impl ProgramDescription {
    /// Map this ProgramDescription into RAM.
    /// The program may already have been relocated, and so may be
    /// either on SPI flash or in RAM.  The `load_offset` argument
    /// that is passed in should be used instead of `self.load_offset`
    /// for this reason.
    pub fn load(
        &self,
        allocator: &mut BootConfig,
        load_offset: u32,
        is_kernel: bool,
        processes: &mut SystemServices,
    ) -> u32 {
        let initial_pid = if is_kernel { 0 } else { 1 };
        // Not a great algorithm!
        for pid in (initial_pid as usize)..processes.processes.len() {
            // The upper bit indicates whether the SATP is valid or not.
            // If this bit is set, then this process is allocated
            if processes.processes[pid].satp & 0x80000000 != 0 {
                continue;
            }

            // Allocate a page to handle the top-level memory translation
            let satp = allocator.alloc() as u32;
            allocator.change_owner(pid as XousPid, satp);
            processes.processes[pid].satp = satp;

            // Turn the satp address into a pointer
            let satp = unsafe { &mut *(satp as *mut PageTable) };

            // Allocate a page for stack
            let sp_page = allocator.alloc() as u32;
            allocator.map_page(satp, sp_page, self.stack_offset, FLG_W | FLG_R);
            allocator.change_owner(pid as XousPid, sp_page);

            assert!((self.load_offset & (PAGE_SIZE - 1)) == 0);
            assert!((self.data_offset & (PAGE_SIZE - 1)) == 0);

            // Map the process text section into RAM.
            // Either this is on SPI flash at an aligned address, or it
            // has been copied into RAM already.  This is why we ignore `self.load_offset`
            // and use the `load_offset` parameter instead.
            for offset in (0..self.load_size).step_by(PAGE_SIZE as usize) {
                allocator.map_page(satp, load_offset + offset, self.text_offset + offset, FLG_W | FLG_R | FLG_X | FLG_U);
                allocator.change_owner(pid as XousPid, load_offset + offset);
            }

            // Map the process data section into RAM.
            for offset in (0..self.data_size).step_by(PAGE_SIZE as usize) {
                let page_addr = allocator.alloc();
                allocator.map_page(satp, page_addr as u32, self.data_offset + offset, FLG_W | FLG_R | FLG_U);
                allocator.change_owner(pid as XousPid, load_offset + offset);
            }
            processes.processes[pid].pc = self.entrypoint;
            processes.processes[pid].state = 1;

            return self.entrypoint;
        }
        panic!("no free PID found");
    }
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
        read_next_tag(b8, &mut byte_offset).expect("couldn't read initial tag");
    if tag_name != make_type!("XArg") || size != 20 {
        panic!("XArg wasn't first tag, or was invalid size");
    }
    let total_bytes = unsafe { (b8 as *const usize).add(byte_offset / 4).read() } * 4;
    cfg.sram_start = unsafe { (b8.add(byte_offset + 8) as *mut u32).read() } as *mut u32;
    cfg.sram_size = unsafe { (b8.add(byte_offset + 12) as *mut u32).read() };
    byte_offset += size as usize;

    cfg.args_size = total_bytes as u32;
    let mut kernel_seen = false;
    let mut init_seen = false;

    while byte_offset < total_bytes {
        let (tag_name, _crc, size) =
            read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
        if tag_name == make_type!("MBLK") {
            cfg.regions_start = unsafe { b8.add(byte_offset) as *mut u32 };
            cfg.regions_size = size;
        } else if tag_name == make_type!("Bflg") {
            let boot_flags = unsafe { (b8.add(byte_offset) as *mut u32).read() };
            if boot_flags & 1 != 0 {
                cfg.no_copy = true;
            }
            if boot_flags & 2 != 0 {
                cfg.base_addr = 0 as *const u32;
            }
        } else if tag_name == make_type!("XKRN") {
            assert!(!kernel_seen, "kernel appears twice");
            assert!(size == 28, "invalid XKRN size");
            kernel_seen = true;
        } else if tag_name == make_type!("Init") {
            assert!(size == 28, "invalid Init size");
            init_seen = true;
        }
        byte_offset += size as usize;
    }

    assert!(kernel_seen, "no kernel definition");
    assert!(init_seen, "no initial programs found");
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
            let prog = unsafe { &*(args.add(byte_offset) as *const ProgramDescription) };

            // Round it off to a page boundary
            let load_size_rounded = (prog.load_size + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            cfg.init_size += load_size_rounded;
            unsafe {
                top = top.sub(load_size_rounded as usize);
                let base = cfg.base_addr.add(prog.load_offset as usize / 4);
                memcpy(top, base, prog.load_size as usize);
                bzero(
                    top.add(prog.load_size as usize / 4),
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
#[export_name = "rust_entry"]
pub unsafe extern "C" fn rust_entry(arg_buffer: *const u8, signature: u32) -> ! {
    stage1(arg_buffer, signature);
}

impl BootConfig {
    fn get_top(&self) -> *mut u32 {
        unsafe {
            self.sram_start
                .add((self.sram_size - self.init_size) as usize / 4)
        }
    }

    /// Zero-alloc a new page, mark it as owned by PID1, and return it.
    /// Decrement the `next_page_offset` (npo) variable by one page.
    pub fn alloc(&mut self) -> *mut u32 {
        let pg = self.get_top();
        self.init_size += PAGE_SIZE;
        unsafe {
            // Grab the page address and zero it out
            bzero(pg as *mut u32, pg.add(PAGE_SIZE as usize) as *mut u32);

            // Mark this page as in-use by PID1
            self.runtime_page_tracker
                .add((self.init_size / PAGE_SIZE) as usize)
                .write_volatile(1);
        };

            // Return the address
            pg as *mut u32
    }

    pub fn change_owner(
        &mut self,
        pid: XousPid,
        region: u32,
    ) {
        // First, check to see if the region is in RAM,
        if region > self.sram_start as u32 && region < self.sram_start as u32 + self.sram_size {
            unsafe {
                self.runtime_page_tracker
                .add(((region - self.sram_start as u32) / PAGE_SIZE) as usize)
                .write_volatile(pid);
            }
            return;
        }

        // The region isn't in RAM, so check the other memory regions.
        let mut runtime_page_tracker_len = self.sram_size * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;

        for region_offset in (0..(self.regions_size / 4) as usize).step_by(3) {
            let region_start = unsafe { self.regions_start.add(region_offset + 0).read() };
            let region_length = unsafe { self.regions_start.add(region_offset + 1).read() };
            // let _region_name = cfg.regions_start.add(region_offset + 2).read();
            if region >= region_start && region < region_start + region_length {
                unsafe {
                    self.runtime_page_tracker
                    .add((runtime_page_tracker_len + ((region - region_start) / PAGE_SIZE)) as usize)
                    .write_volatile(pid);
                }
                return;
            }
            runtime_page_tracker_len += region_length * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;
        }
        panic!("Tried to change region {:08x} that isn't in the memory region!", region);
    }

    /// Map the given page to the specified process table.  If necessary,
    /// allocate a new page.
    ///
    /// # Panics
    ///
    /// * If you try to map a page twice
    pub fn map_page(&mut self, root: &mut PageTable, phys: u32, virt: u32, flags: u32) {
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
        l0_pt[vpn0 as usize] = (ppn1 << 20) | (ppn0 << 10) | flags | FLG_VALID | FLG_D | FLG_A;
        // 1 | 0xe | 0xd0;
    }
}

/// Allocate and initialize memory regions.
/// Returns a pointer to the start of the memory region.
fn allocate_regions(cfg: &mut BootConfig) -> (*mut XousPid, u32) {
    let top = cfg.get_top();
    // Number of individual pages in the system
    let mut runtime_page_tracker_len = cfg.sram_start as u32 * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;

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
    cfg.runtime_page_tracker = runtime_page_tracker as *mut XousPid;
    cfg.runtime_page_tracker_len = runtime_page_tracker_len;

    (runtime_page_tracker as *mut XousPid, runtime_page_tracker_len)
}

fn allocate_processes(cfg: &mut BootConfig) -> *mut SystemServices {
    let runtime_process_table_len = mem::size_of::<SystemServices>() as u32;
    // Allocate the process table
    cfg.init_size += runtime_process_table_len;
    let runtime_process_table = cfg.get_top();
    unsafe {
        bzero(
            runtime_process_table,
            runtime_process_table.add((runtime_process_table_len / 4) as usize),
        );
    }
    runtime_process_table as *mut SystemServices
}

fn allocate_config(cfg: &mut BootConfig) -> &mut BootConfig {
    cfg.init_size += mem::size_of::<BootConfig>() as u32;
    let top = cfg.get_top();
    unsafe { memcpy(top, cfg as *const BootConfig as *const u32, mem::size_of::<BootConfig>()) };
    unsafe { &mut (*(top as *mut BootConfig)) }
}

fn copy_args(cfg: &mut BootConfig, arg_buffer: *const u8) {
    // Copy the args list to target RAM
    cfg.init_size += cfg.args_size;
    let runtime_arg_buffer = cfg.get_top();
    unsafe {
        memcpy(
            runtime_arg_buffer,
            arg_buffer as *mut u32,
            cfg.args_size as usize,
        )
    };
    // TODO: Patch up regions_start
    cfg.args_start = runtime_arg_buffer as *const u8;
}

fn stage1(arg_buffer: *const u8, _signature: u32) -> ! {
    // Store the initial boot config on the stack.  We don't know
    // where in heap this memory will go.
    let mut cfg = BootConfig {
        no_copy: false,
        base_addr: arg_buffer as *const u32,
        regions_start: 0 as *mut u32,
        regions_size: 0,
        sram_start: 0 as *mut u32,
        sram_size: 0,
        args_start: 0 as *const u8,
        args_size: 0,
        init_size: 0,
        runtime_page_tracker: 0 as *mut XousPid,
        runtime_page_tracker_len: 0,
        system_services: 0 as *mut SystemServices,
        process_offset: 0,
    };
    read_initial_config(arg_buffer, &mut cfg);

    // Allocate a stack pointer.
    // Allocate us a stack pointer directly below the memory page tracker,
    // and enable it.
    let sp = unsafe { cfg.get_top().sub(1) };
    cfg.init_size += PAGE_SIZE;

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    allocate_regions(&mut cfg);

    // Processes are also stored in RAM
    cfg.system_services = allocate_processes(&mut cfg);

    // Switch from using our stack-allocated config to a heap-allocated config.
    let mut cfg = allocate_config(&mut cfg);

    // Copy the arguments, if requested
    if !cfg.no_copy {
        copy_args(&mut cfg, arg_buffer);
    }

    // All further allocations must be page-aligned.
    cfg.init_size = (cfg.init_size + 4096 - 1) & !(4096 - 1);

    cfg.process_offset = cfg.init_size;

    // Copy the processes to RAM, if requested.
    if !cfg.no_copy {
        copy_processes(&mut cfg, arg_buffer);
    }

    // Mark all pages as in-use by the kernel.
    // NOTE: This causes the .text section to be owned by PID1!  This
    // will require us to transfer ownership in `stage3`
    for i in 0..(cfg.init_size / PAGE_SIZE) {
        unsafe {
            (cfg.runtime_page_tracker as *mut XousPid)
                .add((cfg.runtime_page_tracker_len - i - 1) as usize)
                .write_volatile(1)
        };
    }

    unsafe { set_sp(sp as u32) };
    stage2(&mut cfg);
}

/// Stage 2 bootloader
/// This sets up the MMU and loads both PID1 and the kernel into RAM.
fn stage2(cfg: &mut BootConfig) -> ! {
    let mut system_services = unsafe { &mut (*cfg.system_services) };

    // Loop through the kernel args and copy the kernel and Init
    let mut args_offset = 0;

    // This is the offset in RAM where programs are loaded from.
    let mut process_offset = cfg.sram_start as u32 + cfg.sram_size - cfg.process_offset;

    // Go through all Init processes and the kernel, setting up their
    // page tables and mapping memory to them.
    while args_offset < cfg.args_size as usize {
        let (tag_name, _crc, size) =
            read_next_tag(cfg.args_start, &mut args_offset).expect("couldn't read next tag");

        if tag_name == make_type!("Init") {
            let init = unsafe { &*(cfg.args_start.add(args_offset) as *const ProgramDescription) };
            init.load(cfg, process_offset, false, &mut system_services);
            let load_size_rounded = (init.load_size + 4096 - 1) & !(4096 - 1);
            process_offset -= load_size_rounded;
        } else if tag_name == make_type!("XKRN") {
            let xkrn = unsafe { &*(cfg.args_start.add(args_offset) as *const ProgramDescription) };
            xkrn.load(cfg, process_offset, true, &mut system_services);
            let load_size_rounded = (xkrn.load_size + 4096 - 1) & !(4096 - 1);
            process_offset -= load_size_rounded;
        }
        args_offset += size as usize;
    }

    // Activate the kernel as the current process, and jump
    // into Supervisor mode.
    loop {}
}
