Require Import isla.isla_lang.
Require Export isla.instructions.memcpy_riscv64.a0.
Require Export isla.instructions.memcpy_riscv64.a4.
Require Export isla.instructions.memcpy_riscv64.a8.
Require Export isla.instructions.memcpy_riscv64.ac.
Require Export isla.instructions.memcpy_riscv64.a10.
Require Export isla.instructions.memcpy_riscv64.a14.
Require Export isla.instructions.memcpy_riscv64.a18.
Require Export isla.instructions.memcpy_riscv64.a1c.

Definition instr_map := [
  (0x0%Z, a0 (* beqz a2,1c <.LBB0_2> *));
  (0x4%Z, a4 (* lb a3,0(a1) *));
  (0x8%Z, a8 (* sb a3,0(a0) *));
  (0xc%Z, ac (* addi a2,a2,-1 *));
  (0x10%Z, a10 (* addi a0,a0,1 *));
  (0x14%Z, a14 (* addi a1,a1,1 *));
  (0x18%Z, a18 (* bnez a2,4 <.LBB0_1> *));
  (0x1c%Z, a1c (* ret *))
].
