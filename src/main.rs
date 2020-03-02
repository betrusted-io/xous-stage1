#![cfg_attr(not(test), no_main)]
#![cfg_attr(not(test), no_std)]

#[macro_use]
mod args;
use args::KernelArguments;

use core::{mem, ptr, slice};

pub type XousPid = u8;
pub const PAGE_SIZE: usize = 4096;
const WORD_SIZE: usize = mem::size_of::<usize>();

const USER_STACK_OFFSET: usize = 0xdfff_fffc;
const PAGE_TABLE_OFFSET: usize = 0x0040_0000;
const PAGE_TABLE_ROOT_OFFSET: usize = 0x0080_0000;
const CONTEXT_OFFSET: usize = 0x0080_1000;
const USER_AREA_START: usize = 0x00c0_0000;

// All of the kernel structures must live within Megapage 0,
// and therefore are limited to 4 MB.
const EXCEPTION_STACK_OFFSET: usize = 0x003f_fffc;
const KERNEL_LOAD_OFFSET: usize = 0x0020_0000;
const KERNEL_ARGUMENT_OFFSET: usize = 0x0010_0000;

const FLG_VALID: usize = 0x1;
const FLG_X: usize = 0x8;
const FLG_W: usize = 0x4;
const FLG_R: usize = 0x2;
const FLG_U: usize = 0x10;
const FLG_A: usize = 0x40;
const FLG_D: usize = 0x80;
const STACK_PAGE_COUNT: usize = 1;

mod debug;

// Install a panic handler when not running tests.
#[cfg(not(test))]
mod panic_handler {
    use core::panic::PanicInfo;
    #[panic_handler]
    fn handle_panic(_arg: &PanicInfo) -> ! {
        // sprintln!("{}", _arg);
        loop {}
    }
}

#[cfg(test)]
mod test;

#[repr(C)]
struct MemoryRegionExtra {
    start: u32,
    length: u32,
    name: u32,
    padding: u32,
}

/// In-memory copy of the configuration page,
/// used by the stage-1 bootloader.
pub struct BootConfig {
    /// `true` if the kernel and Init programs run XIP
    no_copy: bool,

    /// Base load address.  Defaults to the start of the args block
    base_addr: *const usize,

    /// `true` if we should enable the `SUM` bit, allowing the
    /// kernel to access user memory.
    debug: bool,

    /// Where the tagged args list starts in RAM.
    args: KernelArguments,

    /// Additional memory regions in this system
    regions: &'static [MemoryRegionExtra],

    /// The origin of usable memory.  This is where heap lives.
    sram_start: *mut usize,

    /// The size (in bytes) of the heap.
    sram_size: usize,

    /// A running total of the number of bytes consumed during
    /// initialization.  This value, divided by PAGE_SIZE,
    /// indicates the number of pages at the end of RAM that
    /// will need to be owned by the kernel.
    init_size: usize,

    /// Additional pages that are consumed during init.
    /// This includes pages that are allocated to other
    /// processes.
    extra_pages: usize,

    /// This structure keeps track of which pages are owned
    /// and which are free. A PID of `0` indicates it's free.
    runtime_page_tracker: &'static mut [XousPid],

    /// A list of processes that were set up.  The first element
    /// is the kernel, and any subsequent elements are init processes.
    processes: &'static mut [InitialProcess],

    /// The number of 'Init' tags discovered
    init_process_count: usize,
}

impl Default for BootConfig {
    fn default() -> BootConfig {
        BootConfig {
            no_copy: false,
            debug: false,
            base_addr: 0 as *const usize,
            regions: Default::default(),
            sram_start: 0 as *mut usize,
            sram_size: 0,
            args: KernelArguments::new(0 as  *const usize),
            init_size: 0,
            extra_pages: 0,
            runtime_page_tracker: Default::default(),
            init_process_count: 0,
            processes: Default::default(),
        }
    }
}

/// A single RISC-V page table entry.  In order to resolve an address,
/// we need two entries: the top level, followed by the lower level.
#[repr(C)]
pub struct PageTable {
    entries: [usize; PAGE_SIZE / WORD_SIZE],
}

#[repr(C)]
pub struct InitialProcess {
    /// The RISC-V SATP value, which includes the offset of the root page
    /// table plus the process ID.
    satp: usize,

    /// Where execution begins
    entrypoint: usize,

    /// Address of the top of the stack
    sp: usize,
}

/// This describes the kernel as well as initially-loaded processes
#[repr(C)]
pub struct ProgramDescription {
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
    fn start_kernel(
        args: usize,
        ss: usize,
        rpt: usize,
        satp: usize,
        entrypoint: usize,
        stack: usize,
        debug: bool,
    ) -> !;
}

impl ProgramDescription {
    /// Map this ProgramDescription into RAM.
    /// The program may already have been relocated, and so may be
    /// either on SPI flash or in RAM.  The `load_offset` argument
    /// that is passed in should be used instead of `self.load_offset`
    /// for this reason.
    pub fn load(&self, allocator: &mut BootConfig, load_offset: usize, pid: XousPid) {
        assert!(pid != 0);
        println!("Loading program {} into offset {:08x}", pid, load_offset);
        let pid_idx = (pid - 1) as usize;
        let is_kernel = pid == 1;
        let flag_defaults = FLG_R | FLG_W | if is_kernel { 0 } else { FLG_U };
        let stack_addr = USER_STACK_OFFSET;
        if is_kernel {
            assert!(self.text_offset as usize == KERNEL_LOAD_OFFSET);
            assert!(((self.text_offset + self.load_size) as usize) < EXCEPTION_STACK_OFFSET);
            assert!(((self.data_offset + self.data_size) as usize) < EXCEPTION_STACK_OFFSET);
            assert!(self.data_offset as usize >= KERNEL_LOAD_OFFSET);
        } else {
            assert!(self.text_offset as usize >= USER_AREA_START);
            assert!(self.data_offset as usize >= USER_AREA_START);
        }

        // SATP must be nonzero
        if allocator.processes[pid_idx].satp != 0 {
            panic!("tried to re-use a process id");
        }

        // Allocate a page to handle the top-level memory translation
        println!("Allocating");
        let satp_address = allocator.alloc() as usize;
        println!("Changing owner");
        allocator.change_owner(pid as XousPid, satp_address);

        // Turn the satp address into a pointer
        println!("Mapping thingy");
        let satp = unsafe { &mut *(satp_address as *mut PageTable) };
        allocator.map_page(satp, satp_address, PAGE_TABLE_ROOT_OFFSET, FLG_R | FLG_W);

        // Allocate context for this process
        let context_address = allocator.alloc() as usize;
        allocator.map_page(satp, context_address, CONTEXT_OFFSET, FLG_R | FLG_W);

        // Ensure the pagetables are mapped as well
        let pt_addr = allocator.alloc() as usize;
        allocator.map_page(satp, pt_addr, PAGE_TABLE_OFFSET + 0, FLG_R | FLG_W);

        // Allocate stack pages.
        for i in 0..STACK_PAGE_COUNT {
            let sp_page = allocator.alloc() as usize;
            allocator.map_page(
                satp,
                sp_page,
                (stack_addr - PAGE_SIZE * i) & !(PAGE_SIZE - 1),
                flag_defaults,
            );
            allocator.change_owner(pid as XousPid, sp_page);

            // If it's the kernel, also allocate an exception page
            if is_kernel {
                let sp_page = allocator.alloc() as usize;
                allocator.map_page(
                    satp,
                    sp_page,
                    (EXCEPTION_STACK_OFFSET - PAGE_SIZE * i) & !(PAGE_SIZE - 1),
                    flag_defaults,
                );
                allocator.change_owner(pid as XousPid, sp_page);
            }
        }

        assert!((self.text_offset as usize & (PAGE_SIZE - 1)) == 0);
        assert!((self.data_offset as usize & (PAGE_SIZE - 1)) == 0);
        if allocator.no_copy {
            assert!((self.load_offset as usize & (PAGE_SIZE - 1)) == 0);
        }

        // Map the process text section into RAM.
        // Either this is on SPI flash at an aligned address, or it
        // has been copied into RAM already.  This is why we ignore `self.load_offset`
        // and use the `load_offset` parameter instead.
        for offset in (0..self.load_size as usize).step_by(PAGE_SIZE) {
            allocator.map_page(
                satp,
                load_offset + offset,
                self.text_offset as usize + offset,
                flag_defaults | FLG_X,
            );
            allocator.change_owner(pid as XousPid, load_offset + offset);
        }

        // Map the process data section into RAM.
        for offset in (0..self.data_size as usize).step_by(PAGE_SIZE as usize) {
            let page_addr = allocator.alloc();
            allocator.map_page(
                satp,
                page_addr as usize,
                self.data_offset as usize + offset,
                flag_defaults,
            );
            allocator.change_owner(pid as XousPid, load_offset as usize + offset);
        }

        // Our "earlyprintk" equivalent
        if cfg!(feature = "earlyprintk") && is_kernel {
            allocator.map_page(
                satp,
                0xF0002000,
                0x001f_0000,
                FLG_R | FLG_W,
            );
            allocator.change_owner(pid as XousPid, 0xF0002000);
        }

        let ref mut process = allocator.processes[pid_idx];
        process.entrypoint = self.entrypoint as usize;
        process.sp = stack_addr;
        process.satp = 0x80000000 | ((pid as usize) << 22) | (satp_address >> 12);
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

/// Copy _count_ **bytes** from src to dest.
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

pub fn read_initial_config(cfg: &mut BootConfig) {
    let args = cfg.args;
    let mut i = args.iter();
    let xarg = i.next().expect("couldn't read initial tag");
    if xarg.name != make_type!("XArg") || xarg.size != 20 {
        panic!("XArg wasn't first tag, or was invalid size");
    }
    cfg.sram_start = xarg.data[2] as *mut usize;
    cfg.sram_size = xarg.data[3] as usize;

    let mut kernel_seen = false;
    let mut init_seen = false;

    for tag in i {
        if tag.name == make_type!("MREx") {
            cfg.regions = unsafe {
                slice::from_raw_parts(
                    tag.data.as_ptr() as *const MemoryRegionExtra,
                    tag.size as usize / mem::size_of::<MemoryRegionExtra>(),
                )
            };
        } else if tag.name == make_type!("Bflg") {
            let boot_flags = tag.data[0];
            if boot_flags & (1<<0) != 0 {
                cfg.no_copy = true;
            }
            if boot_flags & (1<<1) != 0 {
                cfg.base_addr = 0 as *const usize;
            }
            if boot_flags & (1<<2) != 0 {
                cfg.debug = true;
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
            cfg.init_process_count += 1;
        }
    }

    assert!(kernel_seen, "no kernel definition");
    assert!(init_seen, "no initial programs found");
}

/// Copy program data from the SPI flash into newly-allocated RAM
/// located at the end of memory space.
fn copy_processes(cfg: &mut BootConfig) {
    for tag in cfg.args.iter() {
        if tag.name == make_type!("XKrn") || tag.name == make_type!("Init") {
            let prog = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };

            // Round it off to a page boundary
            let load_size_rounded = (prog.load_size as usize + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            cfg.extra_pages += load_size_rounded / PAGE_SIZE;
            let top = cfg.get_top();
            unsafe {
                // Copy the program to the target address, rounding it off to the load size.
                let src_addr = cfg.base_addr.add(prog.load_offset as usize / mem::size_of::<usize>());
                println!("Loading from {:08x} to {:08x} ({} bytes long)", src_addr as usize, top as usize, prog.load_size);
                memcpy(top, src_addr, prog.load_size as usize);

                // Zero out the remaining data.
                bzero(
                    top.add(prog.load_size as usize / mem::size_of::<usize>()),
                    top.add(load_size_rounded as usize / mem::size_of::<usize>()),
                )
            };
        }
    }
}

impl BootConfig {
    fn get_top(&self) -> *mut usize {
        let val = unsafe {
            self.sram_start
                .add((self.sram_size - self.init_size - self.extra_pages * PAGE_SIZE) / mem::size_of::<usize>())
        };
        assert!((val as usize) >= (self.sram_start as usize));
        assert!((val as usize) < (self.sram_start as usize) + self.sram_size);
        val
    }

    /// Zero-alloc a new page, mark it as owned by PID1, and return it.
    /// Decrement the `next_page_offset` (npo) variable by one page.
    pub fn alloc(&mut self) -> *mut usize {
        self.extra_pages += 1;
        let pg = self.get_top();
        unsafe {
            // Grab the page address and zero it out
            bzero(pg as *mut usize, pg.add(PAGE_SIZE / mem::size_of::<usize>()) as *mut usize);
        }
        // Mark this page as in-use by the kernel
        let extra_bytes = self.extra_pages * PAGE_SIZE;
        self.runtime_page_tracker[(self.sram_size - (extra_bytes + self.init_size)) / PAGE_SIZE] =
            1;

        // Return the address
        pg as *mut usize
    }

    pub fn change_owner(&mut self, pid: XousPid, addr: usize) {
        // First, check to see if the region is in RAM,
        if addr >= self.sram_start as usize && addr < self.sram_start as usize + self.sram_size {
            // Mark this page as in-use by the kernel
            self.runtime_page_tracker[(addr - self.sram_start as usize) / PAGE_SIZE] = pid;
            return;
        }
        // The region isn't in RAM, so check the other memory regions.
        let mut rpt_offset = self.sram_size / PAGE_SIZE;

        for region in self.regions.iter() {
            let rstart = region.start as usize;
            let rlen = region.length as usize;
            if addr >= rstart && addr < rstart + rlen {
                self.runtime_page_tracker[rpt_offset + (addr - rstart) / PAGE_SIZE] = pid;
                return;
            }
            rpt_offset += rlen / PAGE_SIZE;
        }
        panic!(
            "Tried to change region {:08x} that isn't in defined memory!",
            addr
        );
    }

    /// Map the given page to the specified process table.  If necessary,
    /// allocate a new page.
    ///
    /// # Panics
    ///
    /// * If you try to map a page twice
    pub fn map_page(&mut self, root: &mut PageTable, phys: usize, virt: usize, flags: usize) {
        match WORD_SIZE {
            4 => self.map_page_32(root, phys, virt, flags),
            8 => panic!("map_page doesn't work on 64-bit devices"),
            _ => panic!("unrecognized word size: {}", WORD_SIZE),
        }
    }

    pub fn map_page_32(&mut self, root: &mut PageTable, phys: usize, virt: usize, flags: usize) {
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
        if l1_pt[vpn1] & FLG_VALID == 0 {
            new_addr = self.alloc() as usize;
            // Mark this entry as a leaf node (WRX as 0), and indicate
            // it is a valid page by setting "V".
            l1_pt[vpn1] = ((new_addr >> 12) << 10) | FLG_VALID;
        }

        let l0_pt_idx =
            unsafe { &mut (*(((l1_pt[vpn1] << 2) & !((1 << 12) - 1)) as *mut PageTable)) };
        let ref mut l0_pt = l0_pt_idx.entries;

        // Ensure the entry hasn't already been mapped.
        // if l0_pt[vpn0 as usize] & 1 != 0 {
        //     panic!("Page already allocated!");
        // }
        l0_pt[vpn0] = (ppn1 << 20) | (ppn0 << 10) | flags | FLG_VALID | FLG_D | FLG_A;

        // If we had to allocate a level 1 pagetable entry, ensure that it's
        // mapped into our address space.
        if new_addr != 0 {
            self.map_page(
                root,
                new_addr,
                PAGE_TABLE_OFFSET + vpn1 * PAGE_SIZE,
                FLG_R | FLG_W,
            );
        }
    }
}

/// Allocate and initialize memory regions.
/// Returns a pointer to the start of the memory region.
pub fn allocate_regions(cfg: &mut BootConfig) {
    // Number of individual pages in the system
    let mut rpt_pages = cfg.sram_size / PAGE_SIZE;

    for region in cfg.regions.iter() {
        println!(
            "Discovered memory region {:08x} ({:08x} - {:08x}) -- {} bytes",
            region.name,
            region.start,
            region.start + region.length,
            region.length
        );
        let region_length_rounded = (region.length as usize + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
        rpt_pages += region_length_rounded / PAGE_SIZE;
    }

    // Round the tracker to a multiple of the page size, so as to keep memory
    // operations fast.
    rpt_pages = (rpt_pages + mem::size_of::<usize>() - 1) & !(mem::size_of::<usize>() - 1);

    cfg.init_size += rpt_pages * mem::size_of::<XousPid>();

    // Clear all memory pages such that they're not owned by anyone
    let runtime_page_tracker = cfg.get_top();
    assert!((runtime_page_tracker as usize) < (cfg.sram_start as usize) + cfg.sram_size);
    unsafe {
        bzero(
            runtime_page_tracker,
            runtime_page_tracker.add(rpt_pages / mem::size_of::<usize>()),
        );
    }

    cfg.runtime_page_tracker =
        unsafe { slice::from_raw_parts_mut(runtime_page_tracker as *mut XousPid, rpt_pages) };
}

pub fn allocate_processes(cfg: &mut BootConfig) {
    let process_count = cfg.init_process_count + 1;
    let table_size = process_count * mem::size_of::<InitialProcess>();
    // Allocate the process table
    cfg.init_size += table_size;
    let processes = cfg.get_top();
    unsafe {
        bzero(processes, processes.add((table_size / mem::size_of::<usize>()) as usize));
    }
    cfg.processes = unsafe {
        slice::from_raw_parts_mut(processes as *mut InitialProcess, process_count as usize)
    };
}

pub fn copy_args(cfg: &mut BootConfig) {
    // Copy the args list to target RAM
    cfg.init_size += cfg.args.size();
    let runtime_arg_buffer = cfg.get_top();
    unsafe {
        memcpy(
            runtime_arg_buffer,
            cfg.args.base as *const usize,
            cfg.args.size() as usize,
        )
    };
    cfg.args = KernelArguments::new(runtime_arg_buffer);
}

/// Stage 1 Bootloader
/// This makes the program self-sufficient by setting up memory page assignment
/// and copying the arguments to RAM.
/// Assume the bootloader has already set up the stack to point to the end of RAM.
#[export_name = "rust_entry"]
pub unsafe extern "C" fn rust_entry(arg_buffer: *const usize, signature: u32) -> ! {
    let kab = KernelArguments::new(arg_buffer);
    boot_sequence(kab, signature);
}

fn boot_sequence(args: KernelArguments, _signature: u32) -> ! {
    // Store the initial boot config on the stack.  We don't know
    // where in heap this memory will go.
    let mut cfg = BootConfig {
        base_addr: args.base as *const usize,
        args: args,
        ..Default::default()
    };
    read_initial_config(&mut cfg);

    phase_1(&mut cfg);
    phase_2(&mut cfg);

    // The MMU should be set up now, and memory pages assigned to their
    // respective processes.
    let krn_struct_start = cfg.sram_start as usize + cfg.sram_size - cfg.init_size;
    let arg_offset = cfg.args.base as usize - krn_struct_start + KERNEL_ARGUMENT_OFFSET;
    let ip_offset = cfg.processes.as_ptr() as usize - krn_struct_start + KERNEL_ARGUMENT_OFFSET;
    let rpt_offset =
        cfg.runtime_page_tracker.as_ptr() as usize - krn_struct_start + KERNEL_ARGUMENT_OFFSET;
    println!("Jumping to kernel @ {:08x} with map @ {:08x} and stack @ {:08x}",
        cfg.processes[0].satp,
        cfg.processes[0].entrypoint,
        cfg.processes[0].sp,
    );
    unsafe {
        start_kernel(
            arg_offset,
            ip_offset,
            rpt_offset,
            cfg.processes[0].satp,
            cfg.processes[0].entrypoint,
            cfg.processes[0].sp,
            cfg.debug,
        );
    }
}

fn phase_1(cfg: &mut BootConfig) {

    // Allocate space for the stack pointer.
    // The bootloader should have placed the stack pointer at the end of RAM
    // prior to jumping to our program, so allocate one page of data for
    // stack.
    // All other allocations will be placed below the stack pointer.
    cfg.init_size += PAGE_SIZE * 2;

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    println!("Allocating regions");
    allocate_regions(cfg);

    // The kernel, as well as initial processes, are all stored in RAM.
    println!("Allocating processes");
    allocate_processes(cfg);

    // Copy the arguments, if requested
    if cfg.no_copy {
        // TODO: place args into cfg.args
    } else {
        println!("Copying args");
        copy_args(cfg);
    }

    // All further allocations must be page-aligned.
    cfg.init_size = (cfg.init_size + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);

    // Additionally, from this point on all allocations come from
    // their respective processes rather than kernel memory.

    // Copy the processes to RAM, if requested.
    if !cfg.no_copy {
        println!("Copying processes");
        copy_processes(cfg);
    }

    // Mark all pages as in-use by the kernel.
    // NOTE: This causes the .text section to be owned by the kernel!  This
    // will require us to transfer ownership in `stage3`.
    // Note also that we skip the first index, causing the stack to be
    // returned to the process pool.
    println!("Marking pages as in-use");
    for i in 1..(cfg.init_size / PAGE_SIZE) {
        cfg.runtime_page_tracker[cfg.sram_size / PAGE_SIZE - i] = 1;
    }
}

/// Stage 2 bootloader
/// This sets up the MMU and loads both PID1 and the kernel into RAM.
pub fn phase_2(cfg: &mut BootConfig) {
    let args = cfg.args;

    // This is the offset in RAM where programs are loaded from.
    let mut process_offset = cfg.sram_start as usize + cfg.sram_size - cfg.init_size;

    // Go through all Init processes and the kernel, setting up their
    // page tables and mapping memory to them.
    let mut pid = 2;
    for tag in args.iter() {
        if tag.name == make_type!("Init") {
            println!("Loading program into memory");
            let init = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };
            let load_size_rounded = (init.load_size as usize + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            init.load(cfg, process_offset - load_size_rounded, pid);
            pid += 1;
            process_offset -= load_size_rounded;
        } else if tag.name == make_type!("XKrn") {
            println!("Loading kernel into memory");
            let xkrn = unsafe { &*(tag.data.as_ptr() as *const ProgramDescription) };
            let load_size_rounded = (xkrn.load_size as usize + PAGE_SIZE - 1) & !(PAGE_SIZE - 1);
            xkrn.load(cfg, process_offset - load_size_rounded, 1);
            process_offset -= load_size_rounded;
        }
    }

    println!("Done loading.");
    let krn_struct_start = cfg.sram_start as usize + cfg.sram_size - cfg.init_size;
    let krn_l1_pt_addr = cfg.processes[0].satp << 12;
    assert!(krn_struct_start & (PAGE_SIZE - 1) == 0);
    let krn_pg0_ptr = unsafe { (krn_l1_pt_addr as *const usize).read() };

    // Map boot-generated kernel structures into the kernel
    let satp = unsafe { &mut *(krn_l1_pt_addr as *mut PageTable) };
    for addr in (0..cfg.init_size).step_by(PAGE_SIZE as usize) {
        cfg.map_page(
            satp,
            addr + krn_struct_start,
            addr + KERNEL_ARGUMENT_OFFSET,
            FLG_R | FLG_W,
        );
    }

    // Copy the kernel's "MMU Page 0" into every process.
    // This ensures a context switch into the kernel can
    // always be made, and that the `stvec` is always valid.
    // Since it's a megapage, all we need to do is write
    // the one address to get all 4MB mapped.
    println!("Mapping MMU page 0 to all processes");
    for process in cfg.processes[1..].iter() {
        let l1_pt_addr = process.satp << 12;
        unsafe { (l1_pt_addr as *mut usize).write(krn_pg0_ptr) };
    }

    println!("PID1 pagetables:");
    debug::print_pagetable(cfg.processes[0].satp);
    println!("");
    println!("");
    println!("PID2 pagetables:");
    debug::print_pagetable(cfg.processes[1].satp);
    println!(
        "Runtime Page Tracker: {} bytes",
        cfg.runtime_page_tracker.len()
    );
    cfg.runtime_page_tracker[cfg.sram_size / PAGE_SIZE - 1] = 0;
}
