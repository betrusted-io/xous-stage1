.section .text.init, "ax"
.global _start

_start:
    jal zero, prepare_memory

.global abort
abort:
    j abort
