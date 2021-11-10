Require Import isla.isla_lang.
Require Export isla.instructions.simple_hvc.a80000.
Require Export isla.instructions.simple_hvc.a80004.
Require Export isla.instructions.simple_hvc.a80008.
Require Export isla.instructions.simple_hvc.a8000c.
Require Export isla.instructions.simple_hvc.a80010.
Require Export isla.instructions.simple_hvc.a80014.
Require Export isla.instructions.simple_hvc.a80018.
Require Export isla.instructions.simple_hvc.a8001c.
Require Export isla.instructions.simple_hvc.a80020.
Require Export isla.instructions.simple_hvc.a90000.
Require Export isla.instructions.simple_hvc.a90004.
Require Export isla.instructions.simple_hvc.aa0400.
Require Export isla.instructions.simple_hvc.aa0404.

Definition instr_map := [
  (0x80000%Z, a80000 (* mov x0, #0xa0000 *));
  (0x80004%Z, a80004 (* msr vbar_el2, x0 *));
  (0x80008%Z, a80008 (* mov x0, #0x80000000 *));
  (0x8000c%Z, a8000c (* msr hcr_el2, x0 *));
  (0x80010%Z, a80010 (* mov x0, #0x3c4 *));
  (0x80014%Z, a80014 (* msr spsr_el2, x0 *));
  (0x80018%Z, a80018 (* mov x0, #0x90000 *));
  (0x8001c%Z, a8001c (* msr elr_el2, x0 *));
  (0x80020%Z, a80020 (* eret *));
  (0x90000%Z, a90000 (* mov x0, xzr *));
  (0x90004%Z, a90004 (* hvc #0x0 *));
  (0xa0400%Z, aa0400 (* mov x0, #0x2a *));
  (0xa0404%Z, aa0404 (* eret *))
].
