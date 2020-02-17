.section .text.init, "ax"
.global _start

_start:
    li          t0, 0xffffffff
    csrw        mideleg, t0
    csrw        medeleg, t0

    // Place the stack pointer at the end of RAM
    lw          t0, 16(a0) // SRAM start
    lw          t1, 20(a0) // SRAM length
    add         sp, t0, t1

    // Install a machine mode trap handler
    la          t0, abort
    csrw        mtvec, t0

    // Start Rust
    j   rust_entry

// This is used only in debug mode.
.global abort
abort:
    j           abort

.global start_kernel
start_kernel:
    // Enable external interrupts for both machine and supervisor mode
    # li          t0, 0xa0a
    # csrw        mie, t0

    // Delegate as much as we can supervisor mode
    li          t0, 0xffffffff
    csrw        mideleg, t0
    csrw        medeleg, t0
    # csrw        0xBC0, t0 // Unmask all interrupts

    // Reposition the stack at a fixed offset
    li          sp, 0xdffffffc

    // Enable the MMU (once we issue `mret`) and flush the cache
    csrw        satp, a3
    sfence.vma

    // Return to Supervisor mode (and enable interrupts)
    li		    t0, (1 << 11) | (1 << 5)
    csrw	    mstatus, t0

    // Return to the address pointed to by $a4
    csrw        mepc, a4

    // Issue the return
    mret

.global set_satp
set_satp:
    csrw satp, a0
    ret
