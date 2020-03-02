pub struct Uart {
    pub base: *mut u32,
}

impl Uart {
    pub fn putc(&self, c: u8) {
        unsafe {
            // Wait until TXFULL is `0`
            while self.base.add(1).read_volatile() != 0 {
                ()
            }
            self.base.add(0).write_volatile(c as u32)
        };
    }
}

use core::fmt::{Error, Write};
impl Write for Uart {
    fn write_str(&mut self, s: &str) -> Result<(), Error> {
        for c in s.bytes() {
            self.putc(c);
        }
        Ok(())
    }
}

#[macro_use]
#[cfg(all(not(test), feature = "debug-print"))]
pub mod debug_print_hardware {
    use crate::debug::*;
    pub const SUPERVISOR_UART: Uart = Uart {
        base: 0xF000_1000 as *mut u32,
    };

    #[macro_export]
    macro_rules! print
    {
        ($($args:tt)+) => ({
                use core::fmt::Write;
                let _ = write!(crate::debug::debug_print_hardware::SUPERVISOR_UART, $($args)+);
        });
    }
}

#[macro_use]
#[cfg(all(not(test), not(feature = "debug-print")))]
mod debug_print_hardware {
    #[macro_export]
    #[allow(unused_variables)]
    macro_rules! print {
        ($($args:tt)+) => ({
            ()
        });
    }
}

#[macro_export]
macro_rules! println
{
    () => ({
        print!("\r\n")
    });
    ($fmt:expr) => ({
        print!(concat!($fmt, "\r\n"))
    });
    ($fmt:expr, $($args:tt)+) => ({
        print!(concat!($fmt, "\r\n"), $($args)+)
    });
}

pub fn print_pagetable(root: usize) {
    use crate::PageTable;
    println!(
        "Memory Maps (SATP: {:08x}  Root: {:08x}):",
        root,
        root << 12
    );
    let l1_pt = unsafe { &mut (*((root << 12) as *mut PageTable)) };
    for (i, l1_entry) in l1_pt.entries.iter().enumerate() {
        if *l1_entry == 0 {
            continue;
        }
        let _superpage_addr = i as u32 * (1 << 22);
        println!(
            "    {:4} Superpage for {:08x} @ {:08x} (flags: {:02x})",
            i,
            _superpage_addr,
            (*l1_entry >> 10) << 12,
            l1_entry & 0xff
        );
        // let l0_pt_addr = ((l1_entry >> 10) << 12) as *const u32;
        let l0_pt = unsafe { &mut (*(((*l1_entry >> 10) << 12) as *mut PageTable)) };
        for (j, l0_entry) in l0_pt.entries.iter().enumerate() {
            if *l0_entry == 0 {
                continue;
            }
            let _page_addr = j as u32 * (1 << 12);
            println!(
                "        {:4} {:08x} -> {:08x} (flags: {:02x})",
                j,
                _superpage_addr + _page_addr,
                (*l0_entry >> 10) << 12,
                l0_entry & 0xff
            );
        }
    }
}