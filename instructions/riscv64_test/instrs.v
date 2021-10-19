Require Import isla.isla_lang.
Require Export isla.instructions.riscv64_test.a0.
Require Export isla.instructions.riscv64_test.a4.
Require Export isla.instructions.riscv64_test.a8.
Require Export isla.instructions.riscv64_test.a8_spec.
Require Export isla.instructions.riscv64_test.ac.
Require Export isla.instructions.riscv64_test.ac_spec.
Require Export isla.instructions.riscv64_test.a10.

Definition instr_map := [
  (0x0%Z, a0 (* li a0,0 *));
  (0x4%Z, a4 (* addi a0,a0,1 *));
  (0x8%Z, a8 (* sd a1,8(sp) *));
  (0xc%Z, ac (* ld a1,8(sp) *));
  (0x10%Z, a10 (* beq a0,a1,18 <.END> *))
].
