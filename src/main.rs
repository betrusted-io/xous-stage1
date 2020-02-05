#![no_std]
#![no_main]

use core::{mem, ptr};

macro_rules! make_type {
    ($fcc:expr) => {{
        let mut c: [u8; 4] = Default::default();
        c.copy_from_slice($fcc.as_bytes());
        u32::from_le_bytes(c)
    }};
}

extern "C" {
    fn set_sp(sp: u32);
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

fn read_next_tag(b8: *mut u8, byte_offset: &mut usize) -> Result<(u32, u32, u32), ()> {
    let tag_name = u32::from_le(unsafe { (b8 as *mut u32).add(*byte_offset / 4).read() }) as u32;
    *byte_offset += 4;
    let crc = u16::from_le(unsafe { (b8 as *mut u16).add(*byte_offset / 2).read() }) as u32;
    *byte_offset += 2;
    let size = u16::from_le(unsafe { (b8 as *mut u16).add(*byte_offset / 2).read() }) as u32 * 4;
    *byte_offset += 2;
    Ok((tag_name, crc, size))
}

// fn add_more_memory(
//     b8: *mut u8,
//     tag_name: u32,
//     size: u32,
//     sram_start: &mut u32,
//     sram_len: &mut u32,
// ) -> Result<u32, ()> {
//     let mut offset = 0;
//     let mut required_bytes = 0;

//     if tag_name != make_type!("MBLK") {
//         return Ok(0);
//     }
//     if size < 3 {
//         return Err(());
//     }
//     *sram_start = unsafe { (b8 as *mut u32).add(offset / 4 + 0).read() };
//     *sram_len = unsafe { (b8 as *mut u32).add(offset / 4 + 1).read() };
//     while offset < size as usize {
//         let _start = unsafe { (b8 as *mut u32).add(offset / 4 + 0).read() };
//         let length = unsafe { (b8 as *mut u32).add(offset / 4 + 1).read() };
//         let _name = unsafe { (b8 as *mut u32).add(offset / 4 + 2).read() };
//         offset += 12;

//         required_bytes += length / 4096;
//     }
//     Ok(required_bytes)
// }

fn process_tags(b8: *mut u8) -> Result<(u32, *mut u32, u32), ()> {
    let mut byte_offset = 0;
    let mut mem_start = 0 as *mut u32;
    let mut mem_size = 0;

    let (tag_name, _crc, size) =
        read_next_tag(b8, &mut byte_offset).expect("couldn't read next tag");
    if tag_name != make_type!("XASZ") || size != 4 {
        return Err(());
    }
    let total_bytes = unsafe { (b8 as *mut u32).add(byte_offset / 4).read() } * 4;
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

#[link_section = ".init.rust"]
#[export_name = "prepare_memory"]
pub unsafe extern "C" fn prepare_memory(arg_buffer: *mut u8, _signature: u32) -> ! {
    let (args_size, regions_start, regions_size) = process_tags(arg_buffer).unwrap();

    let sram_start = regions_start.add(0 * 3 + 0).read();
    let sram_len = regions_start.add(0 * 3 + 1).read();

    // Number of individual pages in the system
    let mut mem_page_count = 0;
    for region_offset in (0..(regions_size / 4) as usize).step_by(3) {
        let _region_start = regions_start.add(region_offset + 0).read();
        let region_length = regions_start.add(region_offset + 1).read();
        let _region_name = regions_start.add(region_offset + 2).read();
        mem_page_count += region_length * mem::size_of::<u8>() as u32 / 4096;
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
    let memory_pages = runtime_arg_buffer.sub((mem_page_count / 4) as usize);
    bzero(
        memory_pages,
        memory_pages.add((mem_page_count / 4) as usize),
    );

    // Mark these pages as being owned by PID1.
    // Add an extra page to store the program counter in.
    for offset in (sram_len - args_size - mem_page_count - 1) / 4096..(sram_len / 4096) {
        (memory_pages as *mut u8).add(offset as usize).write(1);
    }

    // Up until now we've been using the stack pointer from the bootloader.
    // Allocate us a stack pointer and enable it.
    let sp = (memory_pages as u32 & !(4096 - 1)) - 4;
    set_sp(sp);

    loop {}
}
