From isla Require Import isla_lang.
Require Export isla.instructions.memcpy.a0.
Require Export isla.instructions.memcpy.a4.
Require Export isla.instructions.memcpy.a8.
Require Export isla.instructions.memcpy.ac.
Require Export isla.instructions.memcpy.a10.
Require Export isla.instructions.memcpy.a14.
Require Export isla.instructions.memcpy.a18.
Require Export isla.instructions.memcpy.a1c.

Definition instr_map := [
  (0x0%Z, a0 (* cbz x2, 1c <mcpy+0x1c> *));
  (0x4%Z, a4 (* mov x3, #0x0 *));
  (0x8%Z, a8 (* ldrb w4, [x1, x3] *));
  (0xc%Z, ac (* strb w4, [x0, x3] *));
  (0x10%Z, a10 (* add x3, x3, #0x1 *));
  (0x14%Z, a14 (* cmp x2, x3 *));
  (0x18%Z, a18 (* b.ne 8 <mcpy+0x8> *));
  (0x1c%Z, a1c (* ret *))
].
