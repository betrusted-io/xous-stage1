#![no_std]
#![no_main]

mod args;
use args::KernelArguments;

use core::{mem, ptr};

pub type XousPid = u8;
const PAGE_SIZE: u32 = 4096;
const STACK_OFFSET: u32 = 0xdffffffc;
const MAX_PROCESS_COUNT: usize = 255;

const FLG_VALID: u32 = 0x1;
const FLG_X: u32 = 0x8;
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
    args_base: *const u32,

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
    /// will need to be owned by the kernel.
    init_size: u32,

    /// Additional pages that are consumed during init.
    /// This includes pages that are allocated to other
    /// processes.
    extra_pages: u32,

    /// This structure keeps track of which pages are owned
    /// and which are free. A PID of `0` indicates it's free.
    runtime_page_tracker: *mut XousPid,

    /// The size (in bytes) of the `runtime_page_tracker`.
    runtime_page_tracker_len: u32,

    /// A list of system services.  Effectively, this contains
    /// the process table.
    system_services: *mut SystemServices,
}

/// A single RISC-V page table entry.  In order to resolve an address,
/// we need two entries: the top level, followed by the lower level.
struct PageTable {
    entries: [u32; 1024],
}

struct Process {
    /// The absolute MMU address.  If 0, then this process is free.
    satp: u32,

    /// Currently unused
    _reserved: u32,

    /// Where this process is in terms of lifecycle
    state: u32,

    /// The last address of the program counter
    pc: u32,
}

/// A big unifying struct containing all of the system state
struct SystemServices {
    /// A table of all processes on the system
    processes: [Process; MAX_PROCESS_COUNT],
}

/// This describes the kernel as well as initially-loaded processes
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
}

extern "C" {
    fn start_kernel(args: u32, ss: u32, rpt: u32, satp: u32, entrypoint: u32) -> !;
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
        let flag_defaults = FLG_R | FLG_W | if is_kernel { 0 } else { FLG_U };
        // Not a great algorithm!
        for pid in (initial_pid as usize)..processes.processes.len() {
            // SATP must be nonzero
            if processes.processes[pid].satp != 0 {
                continue;
            }

            // Allocate a page to handle the top-level memory translation
            let satp_address = allocator.alloc() as u32;
            allocator.change_owner(pid as XousPid, satp_address);
            processes.processes[pid].satp = satp_address;

            // Turn the satp address into a pointer
            let satp = unsafe { &mut *(satp_address as *mut PageTable) };
            allocator.map_page(
                satp,
                satp_address,
                0x0020_0000,
                FLG_R | FLG_W,
            );

            // Allocate a page for stack
            let sp_page = allocator.alloc() as u32;
            allocator.map_page(
                satp,
                sp_page,
                STACK_OFFSET & !(PAGE_SIZE - 1),
                flag_defaults,
            );
            allocator.change_owner(pid as XousPid, sp_page);

            // XXX FIXME: allocate a second page
            let sp_page = allocator.alloc() as u32;
            allocator.map_page(
                satp,
                sp_page,
                (STACK_OFFSET - 4096) & !(PAGE_SIZE - 1),
                flag_defaults,
            );
            allocator.change_owner(pid as XousPid, sp_page);

            assert!((self.text_offset & (PAGE_SIZE - 1)) == 0);
            assert!((self.data_offset & (PAGE_SIZE - 1)) == 0);
            if allocator.no_copy {
                assert!((self.load_offset & (PAGE_SIZE - 1)) == 0);
            }

            // Map the process text section into RAM.
            // Either this is on SPI flash at an aligned address, or it
            // has been copied into RAM already.  This is why we ignore `self.load_offset`
            // and use the `load_offset` parameter instead.
            for offset in (0..self.load_size).step_by(PAGE_SIZE as usize) {
                allocator.map_page(
                    satp,
                    load_offset + offset,
                    self.text_offset + offset,
                    flag_defaults | FLG_X,
                );
                allocator.change_owner(pid as XousPid, load_offset + offset);
            }

            // Map the process data section into RAM.
            for offset in (0..self.data_size).step_by(PAGE_SIZE as usize) {
                let page_addr = allocator.alloc();
                allocator.map_page(
                    satp,
                    page_addr as u32,
                    self.data_offset + offset,
                    flag_defaults,
                );
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

fn read_initial_config(args: &KernelArguments, cfg: &mut BootConfig) {
    let mut i = args.iter();
    let xarg = i.next().expect("couldn't read initial tag");
    if xarg.name != make_type!("XArg") || xarg.size != 20 {
        panic!("XArg wasn't first tag, or was invalid size");
    }
    cfg.sram_start = xarg.data[2] as *mut u32;
    cfg.sram_size = xarg.data[3];

    let mut kernel_seen = false;
    let mut init_seen = false;

    for tag in i {
        if tag.name == make_type!("MREx") {
            cfg.regions_start = tag.data.as_ptr() as *mut u32;
            cfg.regions_size = tag.size;
        } else if tag.name == make_type!("Bflg") {
            let boot_flags = tag.data[0];
            if boot_flags & 1 != 0 {
                cfg.no_copy = true;
            }
            if boot_flags & 2 != 0 {
                cfg.base_addr = 0 as *const u32;
            }
        } else if tag.name == make_type!("XKrn") {
            assert!(!kernel_seen, "kernel appears twice");
            assert!(
                tag.size as usize == mem::size_of::<ProgramDescription>(),
                "invalid XKrn size"
            );
            kernel_seen = true;
        } else if tag.name == make_type!("Init") {
            assert!(
                tag.size as usize == mem::size_of::<ProgramDescription>(),
                "invalid Init size"
            );
            init_seen = true;
        }
    }

    assert!(kernel_seen, "no kernel definition");
    // assert!(init_seen, "no initial programs found");
}

fn copy_processes(cfg: &mut BootConfig, args: &KernelArguments) {
    for tag in args.iter() {
        if tag.name == make_type!("XKrn") || tag.name == make_type!("Init") {
            let prog = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };

            // Round it off to a page boundary
            let load_size_rounded = (prog.load_size + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            cfg.extra_pages += load_size_rounded / PAGE_SIZE;
            let top = cfg.get_top();
            unsafe {
                let base = cfg.base_addr.add(prog.load_offset as usize / 4);
                memcpy(top, base, prog.load_size as usize);
                bzero(
                    top.add(prog.load_size as usize / 4),
                    top.add(load_size_rounded as usize / 4),
                )
            };
        }
    }
}

impl BootConfig {
    fn get_top(&self) -> *mut u32 {
        unsafe {
            self.sram_start
                .add((self.sram_size - self.init_size - self.extra_pages * PAGE_SIZE) as usize / 4)
        }
    }

    /// Zero-alloc a new page, mark it as owned by PID1, and return it.
    /// Decrement the `next_page_offset` (npo) variable by one page.
    pub fn alloc(&mut self) -> *mut u32 {
        self.extra_pages += 1;
        let pg = self.get_top();
        unsafe {
            // Grab the page address and zero it out
            bzero(pg as *mut u32, pg.add(PAGE_SIZE as usize / 4) as *mut u32);

            // Mark this page as in-use by PID1
            self.runtime_page_tracker
                .add((self.extra_pages + self.init_size / PAGE_SIZE) as usize)
                .write_volatile(1);
        };

        // Return the address
        pg as *mut u32
    }

    pub fn change_owner(&mut self, pid: XousPid, region: u32) {
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
        let mut runtime_page_tracker_len =
            self.sram_size * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;

        for region_offset in (0..(self.regions_size / 4) as usize).step_by(3) {
            let region_start = unsafe { self.regions_start.add(region_offset + 0).read() };
            let region_length = unsafe { self.regions_start.add(region_offset + 1).read() };
            // let _region_name = cfg.regions_start.add(region_offset + 2).read();
            if region >= region_start && region < region_start + region_length {
                unsafe {
                    self.runtime_page_tracker
                        .add(
                            (runtime_page_tracker_len + ((region - region_start) / PAGE_SIZE))
                                as usize,
                        )
                        .write_volatile(pid);
                }
                return;
            }
            runtime_page_tracker_len +=
                region_length * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;
        }
        panic!(
            "Tried to change region {:08x} that isn't in the memory region!",
            region
        );
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
        let mut new_addr = 0;

        // Allocate a new level 1 pagetable entry if one doesn't exist.
        if l1_pt[vpn1 as usize] & FLG_VALID == 0 {
            new_addr = self.alloc() as u32;

            // Mark this entry as a leaf node (WRX as 0), and indicate
            // it is a valid page by setting "V".
            let ppn = new_addr >> 12;
            l1_pt[vpn1 as usize] = (ppn << 10) | FLG_VALID;
        }

        let l0_pt_idx =
            unsafe { &mut (*(((l1_pt[vpn1 as usize] << 2) & !((1 << 12) - 1)) as *mut PageTable)) };
        let ref mut l0_pt = l0_pt_idx.entries;

        // Ensure the entry hasn't already been mapped.
        // if l0_pt[vpn0 as usize] & 1 != 0 {
        //     panic!("Page already allocated!");
        // }
        l0_pt[vpn0 as usize] = (ppn1 << 20) | (ppn0 << 10) | flags | FLG_VALID | FLG_D | FLG_A;

        // If we had to allocate a level 1 pagetable entry, ensure that it's
        // mapped into our address space.
        if new_addr != 0 {
            self.map_page(
                root,
                new_addr,
                0x0040_0000 + vpn1*PAGE_SIZE,
                FLG_R | FLG_W,
            );
        }
    }
}

/// Allocate and initialize memory regions.
/// Returns a pointer to the start of the memory region.
fn allocate_regions(cfg: &mut BootConfig) -> (*mut XousPid, u32) {
    // Number of individual pages in the system
    let mut runtime_page_tracker_len =
        cfg.sram_size as u32 * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;

    for region_offset in (0..(cfg.regions_size / 4) as usize).step_by(3) {
        // let _region_start = cfg.regions_start.add(region_offset + 0).read();
        let region_length = unsafe { cfg.regions_start.add(region_offset + 1).read() };
        // let _region_name = cfg.regions_start.add(region_offset + 2).read();
        runtime_page_tracker_len += region_length * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;
    }
    cfg.init_size += runtime_page_tracker_len;

    // Clear all memory pages such that they're not owned by anyone
    let runtime_page_tracker = cfg.get_top();
    unsafe {
        bzero(
            runtime_page_tracker,
            runtime_page_tracker.add((runtime_page_tracker_len / 4) as usize),
        );
    }

    cfg.runtime_page_tracker = runtime_page_tracker as *mut XousPid;
    cfg.runtime_page_tracker_len = runtime_page_tracker_len;

    (
        runtime_page_tracker as *mut XousPid,
        runtime_page_tracker_len,
    )
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
    unsafe {
        memcpy(
            top,
            cfg as *const BootConfig as *const u32,
            mem::size_of::<BootConfig>(),
        )
    };
    unsafe { &mut (*(top as *mut BootConfig)) }
}

fn copy_args(cfg: &mut BootConfig, args: &KernelArguments) {
    // Copy the args list to target RAM
    cfg.init_size += args.size();
    let runtime_arg_buffer = cfg.get_top();
    unsafe { memcpy(runtime_arg_buffer, args.base, args.size() as usize) };
    // TODO: Patch up regions_start
    cfg.args_base = runtime_arg_buffer;
}

/// Stage 1 Bootloader
/// This makes the program self-sufficient by setting up memory page assignment
/// and copying the arguments to RAM.
/// Assume the bootloader has already set up the stack to point to the end of RAM.
#[export_name = "rust_entry"]
pub unsafe extern "C" fn rust_entry(arg_buffer: *const u32, signature: u32) -> ! {
    stage1(KernelArguments::new(arg_buffer), signature);
}

fn stage1(args: KernelArguments, _signature: u32) -> ! {
    // Store the initial boot config on the stack.  We don't know
    // where in heap this memory will go.
    let mut cfg = BootConfig {
        no_copy: false,
        base_addr: args.base,
        regions_start: 0 as *mut u32,
        regions_size: 0,
        sram_start: 0 as *mut u32,
        sram_size: 0,
        args_base: args.base,
        init_size: 0,
        extra_pages: 0,
        runtime_page_tracker: 0 as *mut XousPid,
        runtime_page_tracker_len: 0,
        system_services: 0 as *mut SystemServices,
    };
    read_initial_config(&args, &mut cfg);

    // Allocate space for the stack pointer.
    // The bootloader should have placed the stack pointer at the end of RAM
    // prior to jumping to our program, so allocate one page of data for
    // stack.
    // All other allocations will be placed below the stack pointer.
    cfg.init_size += PAGE_SIZE;

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    allocate_regions(&mut cfg);

    // Processes are also stored in RAM
    cfg.system_services = allocate_processes(&mut cfg);

    // Switch from using our stack-allocated config to a heap-allocated config.
    let mut cfg = allocate_config(&mut cfg);

    // Copy the arguments, if requested
    if cfg.no_copy {
        // TODO: place args into cfg.args
    } else {
        copy_args(&mut cfg, &args);
    }

    // All further allocations must be page-aligned.
    cfg.init_size = (cfg.init_size + 4096 - 1) & !(4096 - 1);

    // Additionally, from this point on all allocations come from
    // their respective processes rather than kernel memory.

    // Copy the processes to RAM, if requested.
    if !cfg.no_copy {
        copy_processes(&mut cfg, &args);
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

    stage2(&mut cfg);
}

/// Stage 2 bootloader
/// This sets up the MMU and loads both PID1 and the kernel into RAM.
fn stage2(cfg: &mut BootConfig) -> ! {
    let mut system_services = unsafe { &mut (*cfg.system_services) };
    let args = KernelArguments::new(cfg.args_base);

    // This is the offset in RAM where programs are loaded from.
    let mut process_offset = cfg.sram_start as u32 + cfg.sram_size - cfg.init_size;

    // Go through all Init processes and the kernel, setting up their
    // page tables and mapping memory to them.
    let mut kernel_text_poffset = 0;
    let mut kernel_text_voffset = 0;
    let mut kernel_text_size = 0;
    let mut kernel_data_poffset = 0;
    let mut kernel_data_voffset = 0;
    let mut kernel_data_size = 0;
    for tag in args.iter() {
        if tag.name == make_type!("Init") {
            let init = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };
            let load_size_rounded = (init.load_size + 4096 - 1) & !(4096 - 1);
            init.load(
                cfg,
                process_offset - load_size_rounded,
                false,
                &mut system_services,
            );
            process_offset -= load_size_rounded;
        } else if tag.name == make_type!("XKrn") {
            let xkrn = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };
            let load_size_rounded = (xkrn.load_size + 4096 - 1) & !(4096 - 1);
            kernel_text_size = load_size_rounded;
            kernel_text_poffset = process_offset - kernel_text_size;
            kernel_text_voffset = xkrn.text_offset;
            kernel_data_size = xkrn.data_size;
            kernel_data_poffset = kernel_text_poffset - kernel_data_size;
            kernel_data_voffset = xkrn.data_offset;
            xkrn.load(
                cfg,
                process_offset - load_size_rounded,
                true,
                &mut system_services,
            );
            process_offset -= load_size_rounded;
        }
    }

    let krn_struct_start = cfg.sram_start as u32 + cfg.sram_size - cfg.init_size;
    for pid in system_services.processes.iter() {
        if pid.satp == 0 {
            continue;
        }
        // Map kernel structures to each allocated process space
        let satp = unsafe { &mut *(pid.satp as *mut PageTable) };
        for (off, addr) in (0..cfg.init_size).step_by(PAGE_SIZE as usize).enumerate() {
            cfg.map_page(
                satp,
                krn_struct_start + addr,
                off as u32 * PAGE_SIZE + 0x00100000,
                FLG_R | FLG_W,
            );
        }

        // Map the kernel text section into every process
        for offset in (0..kernel_text_size).step_by(PAGE_SIZE as usize) {
            cfg.map_page(
                satp,
                kernel_text_poffset + offset,
                kernel_text_voffset + offset,
                FLG_R | FLG_W | FLG_X,
            );
        }

        // Map the kernel data section into every process.
        for offset in (0..kernel_data_size).step_by(PAGE_SIZE as usize) {
            cfg.map_page(
                satp,
                kernel_data_poffset + offset,
                kernel_data_voffset + offset,
                FLG_R | FLG_W,
            );
        }
    }

    let arg_offset = cfg.args_base as u32 - krn_struct_start + 0x00100000;
    let ss_offset = cfg.system_services as u32 - krn_struct_start + 0x00100000;
    let rpt_offset = cfg.runtime_page_tracker as u32 - krn_struct_start + 0x00100000;
    unsafe {
        start_kernel(
            arg_offset,
            ss_offset,
            rpt_offset,
            (system_services.processes[0].satp >> 12) | (1 << 31),
            system_services.processes[0].pc,
        );
    }
}
