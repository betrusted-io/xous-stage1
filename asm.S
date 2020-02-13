.section .text.init, "ax"
.global _start

_start:
    li a0, 0x20600000
    // Place the stack pointer at the end of RAM
    lw t0, 16(a0) // SRAM start
    lw t1, 20(a0) // SRAM length

    # Point the stack pointer at the end of RAM
    add sp, t0, t1

    j rust_entry

// This is used only in debug mode.
.global abort
abort:
    j abort

.global set_sp
set_sp:
    add sp,a0,zero
    ret

.global set_satp
set_satp:
    csrw satp, a0
    ret
