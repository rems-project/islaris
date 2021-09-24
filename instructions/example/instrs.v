Require Import isla.isla_lang.
Require Export isla.instructions.example.a0.
Require Export isla.instructions.example.a4.
Require Export isla.instructions.example.a8.
Require Export isla.instructions.example.a10.
Require Export isla.instructions.example.a14.
Require Export isla.instructions.example.a18.
Require Export isla.instructions.example.a1c.
Require Export isla.instructions.example.a20.
Require Export isla.instructions.example.a24.
Require Export isla.instructions.example.a28.
Require Export isla.instructions.example.a2c.
Require Export isla.instructions.example.a34.
Require Export isla.instructions.example.a38.

Definition instr_map := [
  (0x0%Z, a0 (* bl 10 <fn1> *));
  (0x4%Z, a4 (* mov x28, x0 *));
  (0x8%Z, a8 (* str x28, [x27] *));
  (0x10%Z, a10 (* mov w0, #0x0 *));
  (0x14%Z, a14 (* ret *));
  (0x18%Z, a18 (* cmp x1, #0x0 *));
  (0x1c%Z, a1c (* b.ne 28 <branch1> *));
  (0x20%Z, a20 (* mov x0, #0x1 *));
  (0x24%Z, a24 (* b 2c <branch2> *));
  (0x28%Z, a28 (* bl 34 <fn2> *));
  (0x2c%Z, a2c (* mov x28, x0 *));
  (0x34%Z, a34 (* mov x0, #0x0 *));
  (0x38%Z, a38 (* ret *))
].
