.section .text.init, "ax"
.global _start

_start:
    li a0, 0x20600000
    li sp, 0x40100000
    j stage1

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
