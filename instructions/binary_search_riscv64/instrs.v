Require Import isla.isla_lang.
Require Export isla.instructions.binary_search_riscv64.a0.
Require Export isla.instructions.binary_search_riscv64.a4.
Require Export isla.instructions.binary_search_riscv64.a4_spec.
Require Export isla.instructions.binary_search_riscv64.a8.
Require Export isla.instructions.binary_search_riscv64.a8_spec.
Require Export isla.instructions.binary_search_riscv64.ac.
Require Export isla.instructions.binary_search_riscv64.ac_spec.
Require Export isla.instructions.binary_search_riscv64.a10.
Require Export isla.instructions.binary_search_riscv64.a10_spec.
Require Export isla.instructions.binary_search_riscv64.a14.
Require Export isla.instructions.binary_search_riscv64.a14_spec.
Require Export isla.instructions.binary_search_riscv64.a18.
Require Export isla.instructions.binary_search_riscv64.a18_spec.
Require Export isla.instructions.binary_search_riscv64.a1c.
Require Export isla.instructions.binary_search_riscv64.a1c_spec.
Require Export isla.instructions.binary_search_riscv64.a20.
Require Export isla.instructions.binary_search_riscv64.a24.
Require Export isla.instructions.binary_search_riscv64.a28.
Require Export isla.instructions.binary_search_riscv64.a2c.
Require Export isla.instructions.binary_search_riscv64.a30.
Require Export isla.instructions.binary_search_riscv64.a34.
Require Export isla.instructions.binary_search_riscv64.a38.
Require Export isla.instructions.binary_search_riscv64.a3c.
Require Export isla.instructions.binary_search_riscv64.a40.
Require Export isla.instructions.binary_search_riscv64.a44.
Require Export isla.instructions.binary_search_riscv64.a48.
Require Export isla.instructions.binary_search_riscv64.a4c.
Require Export isla.instructions.binary_search_riscv64.a50.
Require Export isla.instructions.binary_search_riscv64.a54.
Require Export isla.instructions.binary_search_riscv64.a58.
Require Export isla.instructions.binary_search_riscv64.a5c.
Require Export isla.instructions.binary_search_riscv64.a60.
Require Export isla.instructions.binary_search_riscv64.a64.
Require Export isla.instructions.binary_search_riscv64.a68.
Require Export isla.instructions.binary_search_riscv64.a6c.
Require Export isla.instructions.binary_search_riscv64.a70.
Require Export isla.instructions.binary_search_riscv64.a74.
Require Export isla.instructions.binary_search_riscv64.a78.
Require Export isla.instructions.binary_search_riscv64.a7c.
Require Export isla.instructions.binary_search_riscv64.a7c_spec.
Require Export isla.instructions.binary_search_riscv64.a80.
Require Export isla.instructions.binary_search_riscv64.a80_spec.
Require Export isla.instructions.binary_search_riscv64.a84.
Require Export isla.instructions.binary_search_riscv64.a84_spec.
Require Export isla.instructions.binary_search_riscv64.a88.
Require Export isla.instructions.binary_search_riscv64.a88_spec.
Require Export isla.instructions.binary_search_riscv64.a8c.
Require Export isla.instructions.binary_search_riscv64.a8c_spec.
Require Export isla.instructions.binary_search_riscv64.a90.
Require Export isla.instructions.binary_search_riscv64.a90_spec.
Require Export isla.instructions.binary_search_riscv64.a94.
Require Export isla.instructions.binary_search_riscv64.a94_spec.
Require Export isla.instructions.binary_search_riscv64.a98.
Require Export isla.instructions.binary_search_riscv64.a9c.
Require Export isla.instructions.binary_search_riscv64.aa0.
Require Export isla.instructions.binary_search_riscv64.aa4.
Require Export isla.instructions.binary_search_riscv64.aa8.

Definition instr_map := [
  (0x0%Z, a0 (* addi sp,sp,-64 *));
  (0x4%Z, a4 (* sd ra,56(sp) *));
  (0x8%Z, a8 (* sd s0,48(sp) *));
  (0xc%Z, ac (* sd s1,40(sp) *));
  (0x10%Z, a10 (* sd s2,32(sp) *));
  (0x14%Z, a14 (* sd s3,24(sp) *));
  (0x18%Z, a18 (* sd s4,16(sp) *));
  (0x1c%Z, a1c (* sd s5,8(sp) *));
  (0x20%Z, a20 (* beqz a2,74 <.LBB0_5> *));
  (0x24%Z, a24 (* mv s2,a3 *));
  (0x28%Z, a28 (* mv s5,a2 *));
  (0x2c%Z, a2c (* mv s3,a1 *));
  (0x30%Z, a30 (* mv s4,a0 *));
  (0x34%Z, a34 (* li s1,0 *));
  (0x38%Z, a38 (* j 44 <.LBB0_3> *));
  (0x3c%Z, a3c (* mv s5,s0 *));
  (0x40%Z, a40 (* bleu s5,s1,78 <.LBB0_6> *));
  (0x44%Z, a44 (* sub a0,s5,s1 *));
  (0x48%Z, a48 (* srli a0,a0,0x1 *));
  (0x4c%Z, a4c (* add s0,a0,s1 *));
  (0x50%Z, a50 (* slli a0,s0,0x3 *));
  (0x54%Z, a54 (* add a0,a0,s3 *));
  (0x58%Z, a58 (* ld a0,0(a0) *));
  (0x5c%Z, a5c (* mv a1,s2 *));
  (0x60%Z, a60 (* jalr s4 *));
  (0x64%Z, a64 (* beqz a0,3c <.LBB0_2> *));
  (0x68%Z, a68 (* addi s1,s0,1 *));
  (0x6c%Z, a6c (* bltu s1,s5,44 <.LBB0_3> *));
  (0x70%Z, a70 (* j 78 <.LBB0_6> *));
  (0x74%Z, a74 (* li s1,0 *));
  (0x78%Z, a78 (* mv a0,s1 *));
  (0x7c%Z, a7c (* ld s5,8(sp) *));
  (0x80%Z, a80 (* ld s4,16(sp) *));
  (0x84%Z, a84 (* ld s3,24(sp) *));
  (0x88%Z, a88 (* ld s2,32(sp) *));
  (0x8c%Z, a8c (* ld s1,40(sp) *));
  (0x90%Z, a90 (* ld s0,48(sp) *));
  (0x94%Z, a94 (* ld ra,56(sp) *));
  (0x98%Z, a98 (* addi sp,sp,64 *));
  (0x9c%Z, a9c (* ret *));
  (0xa0%Z, aa0 (* sltu a0,a1,a0 *));
  (0xa4%Z, aa4 (* xori a0,a0,1 *));
  (0xa8%Z, aa8 (* ret *))
].
