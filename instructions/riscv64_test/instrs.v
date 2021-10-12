Require Import isla.isla_lang.
Require Export isla.instructions.riscv64_test.a0.
Require Export isla.instructions.riscv64_test.a4.
Require Export isla.instructions.riscv64_test.a8.

Definition instr_map := [
  (0x0%Z, a0 (* li a0,0 *));
  (0x4%Z, a4 (* addi a0,a0,1 *));
  (0x8%Z, a8 (* beq a0,a1,10 <.END> *))
].
