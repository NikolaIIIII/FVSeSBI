.section ".text.boot"

.globl _start
_start:
	csrw mie, zero
	la sp, stacks_start
	li t0, 4096
	add sp, sp, t0
	csrw mscratch, sp
	tail sbi_main

.section .data
.align  12
.global stacks_start
stacks_start:
	.skip 4096
