.section .text.init, "ax"
.global _start

_start:
    li a0, 0x20600000
    j stage1

.global abort
abort:
    j abort

.global set_sp
set_sp:
    add sp,a0,zero
    ret
