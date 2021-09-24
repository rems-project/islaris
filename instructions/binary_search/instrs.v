Require Import isla.isla_lang.
Require Export isla.instructions.binary_search.a0.
Require Export isla.instructions.binary_search.a0_spec.
Require Export isla.instructions.binary_search.a4.
Require Export isla.instructions.binary_search.a4_spec.
Require Export isla.instructions.binary_search.a8.
Require Export isla.instructions.binary_search.a8_spec.
Require Export isla.instructions.binary_search.ac.
Require Export isla.instructions.binary_search.ac_spec.
Require Export isla.instructions.binary_search.a10.
Require Export isla.instructions.binary_search.a14.
Require Export isla.instructions.binary_search.a18.
Require Export isla.instructions.binary_search.a1c.
Require Export isla.instructions.binary_search.a20.
Require Export isla.instructions.binary_search.a24.
Require Export isla.instructions.binary_search.a28.
Require Export isla.instructions.binary_search.a2c.
Require Export isla.instructions.binary_search.a2c_spec.
Require Export isla.instructions.binary_search.a30.
Require Export isla.instructions.binary_search.a34.
Require Export isla.instructions.binary_search.a38.
Require Export isla.instructions.binary_search.a3c.
Require Export isla.instructions.binary_search.a40.
Require Export isla.instructions.binary_search.a44.
Require Export isla.instructions.binary_search.a44_spec.
Require Export isla.instructions.binary_search.a48.
Require Export isla.instructions.binary_search.a48_spec.
Require Export isla.instructions.binary_search.a4c.
Require Export isla.instructions.binary_search.a50.
Require Export isla.instructions.binary_search.a54.
Require Export isla.instructions.binary_search.a58.
Require Export isla.instructions.binary_search.a5c.
Require Export isla.instructions.binary_search.a60.
Require Export isla.instructions.binary_search.a60_spec.
Require Export isla.instructions.binary_search.a64.
Require Export isla.instructions.binary_search.a64_spec.
Require Export isla.instructions.binary_search.a68.
Require Export isla.instructions.binary_search.a68_spec.
Require Export isla.instructions.binary_search.a6c.
Require Export isla.instructions.binary_search.a6c_spec.
Require Export isla.instructions.binary_search.a70.
Require Export isla.instructions.binary_search.a74.
Require Export isla.instructions.binary_search.a78.
Require Export isla.instructions.binary_search.a7c.
Require Export isla.instructions.binary_search.a80.
Require Export isla.instructions.binary_search.a84.

Definition instr_map := [
  (0x0%Z, a0 (* stp x29, x30, [sp, #-64]! *));
  (0x4%Z, a4 (* stp x24, x23, [sp, #16] *));
  (0x8%Z, a8 (* stp x22, x21, [sp, #32] *));
  (0xc%Z, ac (* stp x20, x19, [sp, #48] *));
  (0x10%Z, a10 (* mov x29, sp *));
  (0x14%Z, a14 (* cbz x2, 58 <binary_search+0x58> *));
  (0x18%Z, a18 (* mov x19, x3 *));
  (0x1c%Z, a1c (* mov x20, x2 *));
  (0x20%Z, a20 (* mov x21, x1 *));
  (0x24%Z, a24 (* mov x22, x0 *));
  (0x28%Z, a28 (* mov x23, xzr *));
  (0x2c%Z, a2c (* sub x8, x20, x23 *));
  (0x30%Z, a30 (* add x24, x23, x8, lsr #1 *));
  (0x34%Z, a34 (* ldr x0, [x21, x24, lsl #3] *));
  (0x38%Z, a38 (* mov x1, x19 *));
  (0x3c%Z, a3c (* blr x22 *));
  (0x40%Z, a40 (* tst w0, #0x1 *));
  (0x44%Z, a44 (* csel x20, x20, x24, ne *));
  (0x48%Z, a48 (* csinc x23, x23, x24, eq *));
  (0x4c%Z, a4c (* cmp x20, x23 *));
  (0x50%Z, a50 (* b.hi 2c <binary_search+0x2c> *));
  (0x54%Z, a54 (* b 5c <binary_search+0x5c> *));
  (0x58%Z, a58 (* mov x23, xzr *));
  (0x5c%Z, a5c (* mov x0, x23 *));
  (0x60%Z, a60 (* ldp x20, x19, [sp, #48] *));
  (0x64%Z, a64 (* ldp x22, x21, [sp, #32] *));
  (0x68%Z, a68 (* ldp x24, x23, [sp, #16] *));
  (0x6c%Z, a6c (* ldp x29, x30, [sp], #64 *));
  (0x70%Z, a70 (* ret *));
  (0x74%Z, a74 (* ldr x8, [x0] *));
  (0x78%Z, a78 (* ldr x9, [x1] *));
  (0x7c%Z, a7c (* cmp x8, x9 *));
  (0x80%Z, a80 (* cset w0, ls *));
  (0x84%Z, a84 (* ret *))
].
