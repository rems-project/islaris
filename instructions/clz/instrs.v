Require Import isla.isla_lang.
Require Export isla.instructions.clz.a0.
Require Export isla.instructions.clz.a4.

Definition instr_map := [
  (0x0%Z, a0 (* clz x0, x0 *));
  (0x4%Z, a4 (* ret *))
].
