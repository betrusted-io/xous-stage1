#[cfg(test)]
fn get_args_bin() -> &'static [u8] {
    include_bytes!("../test/args.bin")
}

#[test]
fn parse_args_bin() {
    use crate::args::KernelArguments;
    let args = get_args_bin();
    println!("Args is {} bytes long", args.len());
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
