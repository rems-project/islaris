Require Import isla.isla_lang.
Require Export isla.instructions.hello.a0.
Require Export isla.instructions.hello.a4.
Require Export isla.instructions.hello.a8.
Require Export isla.instructions.hello.ac.
Require Export isla.instructions.hello.a10.
Require Export isla.instructions.hello.a14.
Require Export isla.instructions.hello.a18.
Require Export isla.instructions.hello.a1c.

Definition instr_map := [
  (0x0%Z, a0 (* adrp x1, 0 <main> *));
  (0x4%Z, a4 (* mov x2, #0x1000 *));
  (0x8%Z, a8 (* add x1, x1, #0x690 *));
  (0xc%Z, ac (* mov w0, #0x48 *));
  (0x10%Z, a10 (* movk x2, #0x101f, lsl #16 *));
  (0x14%Z, a14 (* strb w0, [x2] *));
  (0x18%Z, a18 (* ldrb w0, [x1, #1]! *));
  (0x1c%Z, a1c (* cbnz w0, 14 <main+0x14> *))
].
