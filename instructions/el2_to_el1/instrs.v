Require Import isla.isla_lang.
Require Export isla.instructions.el2_to_el1.a80000.
Require Export isla.instructions.el2_to_el1.a80004.
Require Export isla.instructions.el2_to_el1.a80008.

Definition instr_map := [
  (0x80000%Z, a80000 (* mov x0, #0x100000 *));
  (0x80004%Z, a80004 (* msr elr_el2, x0 *));
  (0x80008%Z, a80008 (* eret *))
].
