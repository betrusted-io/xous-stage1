
#[test]
fn pass() {
    assert!(true);
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
