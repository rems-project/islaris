.globl _start

_start:
  // Install an exception vector.
  mov x0, 0xa0000
  msr vbar_el2, x0

  // Hypervisor configuration: aarch64 mode for EL1.
  mov x0, 0x80000000
  msr hcr_el2, x0

  // Configure EL1 state (use SP_EL0, no interupts).
  mov x0, 0x3c4
  msr spsr_el2, x0

  mov x0, 0x90000
  msr elr_el2, x0       // (Written to the ELR_EL2 system register.)
  eret                  // Simulate an "exception return" to move to EL1.

.org 0x10000
enter_el1:
  mov x0, xzr           // Zero out x0.
  hvc 0                 // Perform an hypervisor call.
  b .                   // Hang forever in a loop (just in case).

// Our exception vector for EL2.
.org 0x20000
.align 11
el2_exception_vector:
  // Synchronous - Current EL with SP0.
  .align 7
  b .
  // IRQ - Current EL with SP0.
  .align 7
  b .
  // FIQ - Current EL with SP0.
  .align 7
  b .
  // SError - Current EL with SP0.
  .align 7
  b .
  // Synchronous - Current EL with SPx.
  .align 7
  b .
  // IRQ - Current EL with SPx.
  .align 7
  b .
  // FIQ - Current EL with SPx.
  .align 7
  b .
  // SError - Current EL with SPx.
  .align 7
  b .
  // Synchronous - Lower EL with AArch64.
  .align 7
  mov x0, 42
  eret
  // IRQ - Lower EL with AArch64.
  .align 7
  b .
  // FIQ - Lower EL with AArch64.
  .align 7
  b .
  // SError - Lower EL with AArch64.
  .align 7
  b .
  // Synchronous - Lower EL with AArch32.
  .align 7
  b .
  // IRQ - Lower EL with AArch32.
  .align 7
  b .
  // FIQ - Lower EL with AArch32.
  .align 7
  b .
  // SError - Lower EL with AArch32.
  .align 7
  b .
.align 11
