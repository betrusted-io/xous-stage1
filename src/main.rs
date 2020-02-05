#![no_std]
#![no_main]

use core::{mem, ptr};
pub type XousPid = u8;
const PAGE_SIZE: u32 = 4096;

/// A single RISC-V page table entry.  In order to resolve an address,
/// we need two entries: the top level, followed by the lower level.
struct PageTable {
    entries: [u32; 1024],
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

impl ProgramDescription {
    pub fn load(&self, allocator: &mut Allocator, pid1_satp: &mut PageTable, sp_page: u32) -> u32 {
        allocator.map_page(pid1_satp, sp_page, self.stack_offset);
        assert!((self.load_offset & (PAGE_SIZE - 1)) == 0);
        assert!((self.data_offset & (PAGE_SIZE - 1)) == 0);
        for offset in (0..self.load_size).step_by(PAGE_SIZE as usize) {
            let page_addr = allocator.alloc();
            allocator.map_page(pid1_satp, page_addr as u32, self.text_offset + offset);
            let mut to_copy = PAGE_SIZE;
            if self.load_size - offset < to_copy {
                to_copy = self.load_size - offset;
            }
            unsafe { memcpy(page_addr, (self.load_offset + offset) as *mut u32, to_copy as usize) };
        }

        for offset in (0..self.data_size).step_by(PAGE_SIZE as usize) {
            let page_addr = allocator.alloc();
            allocator.map_page(pid1_satp, page_addr as u32, self.data_offset + offset);
        }
        self.entrypoint
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
    fn set_satp(satp: u32);
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

pub unsafe fn memcpy<T>(dest: *mut T, src: *mut T, count: usize)
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

fn process_tags(b8: *const u8) -> Result<(u32, *mut u32, u32), ()> {
    let mut byte_offset = 0;
    let mut mem_start = 0 as *mut u32;
    let mut mem_size = 0;

    let (tag_name, _crc, size) =
        read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
    if tag_name != make_type!("XASZ") || size != 4 {
        return Err(());
    }
    let total_bytes = unsafe { (b8 as *const u32).add(byte_offset / 4).read() } * 4;
    byte_offset += 4;

    let required_bytes = total_bytes;

    loop {
        let (tag_name, _crc, size) =
            read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
        if tag_name == make_type!("MBLK") {
            mem_start = unsafe { b8.add(byte_offset) as *mut u32 };
            mem_size = size;
        }
        byte_offset += size as usize;

        if byte_offset as u32 == total_bytes {
            return Ok((required_bytes, mem_start, mem_size));
        }
        if byte_offset as u32 > total_bytes {
            panic!(
                "exceeded total bytes ({}) with byte_offset of {}",
                total_bytes, byte_offset
            );
        }
    }
}

/// Stage 1 Bootloader
/// This makes the program self-sufficient by setting up memory page assignment
/// and copying the arguments to RAM
#[export_name = "stage1"]
pub unsafe extern "C" fn stage1(arg_buffer: *const u8, _signature: u32) -> ! {
    let (args_size, regions_start, regions_size) = process_tags(arg_buffer).unwrap();

    // The first region is defined as being "main RAM", which will be used
    // to keep track of allocations.
    let sram_start = regions_start.add(0 * 3 + 0).read();
    let sram_len = regions_start.add(0 * 3 + 1).read();

    // Number of individual pages in the system
    let mut mem_page_count = 0;
    for region_offset in (0..(regions_size / 4) as usize).step_by(3) {
        let _region_start = regions_start.add(region_offset + 0).read();
        let region_length = regions_start.add(region_offset + 1).read();
        let _region_name = regions_start.add(region_offset + 2).read();
        mem_page_count += region_length * mem::size_of::<XousPid>() as u32 / PAGE_SIZE;
    }
    // Ensure we have a number of pages divisible by 4, since everything is done
    // with 32-bit math.
    mem_page_count = mem_page_count + ((4 - (mem_page_count & 3)) & 3);

    // Copy the args list to target RAM
    let runtime_arg_buffer = (sram_start + sram_len - args_size) as *mut u32;
    memcpy(
        runtime_arg_buffer,
        arg_buffer as *mut u32,
        args_size as usize,
    );

    // Clear all memory pages such that they're not owned by anyone
    let runtime_page_tracker = runtime_arg_buffer.sub((mem_page_count / 4) as usize);
    bzero(
        runtime_page_tracker,
        runtime_page_tracker.add((mem_page_count / 4) as usize),
    );

    // Drop write permissions for the arg buffer
    let runtime_arg_buffer = runtime_arg_buffer as *const u8;

    // Mark these pages as being owned by PID1.
    // Add an extra page to store the stack pointer, also owned by PID1.
    for offset in (sram_len - args_size - mem_page_count - 1) / PAGE_SIZE..(sram_len / PAGE_SIZE) {
        (runtime_page_tracker as *mut XousPid)
            .add(offset as usize)
            .write(1);
    }

    // Up until now we've been using the stack pointer from the bootloader.
    // Allocate us a stack pointer directly below the memory page tracker,
    // and enable it.
    let sp = (runtime_page_tracker as u32 & !(PAGE_SIZE - 1)) - 4;
    set_sp(sp);

    stage2(
        runtime_arg_buffer,
        args_size,
        runtime_page_tracker as *mut XousPid,
        mem_page_count,
        sram_start as *mut u8,
        sram_len,
    );
}

struct Allocator {
    next_page_offset: u32,
    runtime_page_tracker: *mut XousPid,
    sram_start: *mut u8,
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
    pub fn map_page(
        &mut self,
        root: &mut PageTable,
        phys: u32,
        virt: u32,
    ) {
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

    let pid1_satp = allocator.alloc() as u32;
    unsafe { set_satp((pid1_satp >> 10) | 0x80000000 | (1<<22) ) };
    let pid1_satp = unsafe { &mut *(pid1_satp as *mut PageTable) };

    // Loop through the kernel args and copy the kernel and PID1
    let mut args_offset = 0;
    let mut pid1_seen = false;
    let mut xkrn_seen = false;
    let mut kernel_entrypoint = 0;
    let mut pid1_entrypoint = 0;
    while args_offset < runtime_args_len as usize {
        let (tag_name, _crc, size) =
            read_next_tag(runtime_args, &mut args_offset).expect("couldn't read next tag");
        if tag_name == make_type!("PID1") {
            assert!(!pid1_seen, "pid1 appears twice");
            assert!(size == 28, "invalid PID1 size");
            let pid1 = unsafe { & *(runtime_args.add(args_offset) as *const ProgramDescription) };
            pid1.load(&mut allocator, pid1_satp, sp_page);
            pid1_seen = true;
        }
        if tag_name == make_type!("XKRN") {
            assert!(size == 24, "invalid XKRN size");
            assert!(!xkrn_seen, "xkrn appears twice");
            let xkrn = unsafe { & *(runtime_args.add(args_offset) as *const ProgramDescription) };
            kernel_entrypoint = xkrn.load(&mut allocator, pid1_satp, sp_page);
            xkrn_seen = true;
        }
    }

    loop {}
}
