// Code to transition from EL2 to EL1.
// Assumptions:
// - HCR_EL2 set to something reasonable (bit 31 set),
// - SPSR_EL2 set to something reasonable (e.g., 0x3C4).

.org 0x80000
el2_to_el1:
  mov x0, 0x100000  // Put the address corresponding to enter_el1 in x0.
  msr elr_el2, x0   // Set ELR_EL2 (exception link register) to that address.
  eret              // Simulate an "exception return" to move to EL1.

.org 0x100000
enter_el1:
  nop               // Some dummy instruction at EL1.
