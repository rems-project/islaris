Require Import isla.isla_lang.
Require Export isla.instructions.uart.a80168.
Require Export isla.instructions.uart.a8016c.
Require Export isla.instructions.uart.a80170.
Require Export isla.instructions.uart.a80174.
Require Export isla.instructions.uart.a80178.
Require Export isla.instructions.uart.a8017c.
Require Export isla.instructions.uart.a80180.
Require Export isla.instructions.uart.a80184.
Require Export isla.instructions.uart.a80188.
Require Export isla.instructions.uart.a8018c.
Require Export isla.instructions.uart.a80190.
Require Export isla.instructions.uart.a80194.
Require Export isla.instructions.uart.a80198.
Require Export isla.instructions.uart.a8019c.

Definition instr_map := [
  (0x80168%Z, a80168 (* mov x2, #0x5054 *));
  (0x8016c%Z, a8016c (* and w0, w0, #0xff *));
  (0x80170%Z, a80170 (* movk x2, #0x3f21, lsl #16 *));
  (0x80174%Z, a80174 (* ldr w1, [x2] *));
  (0x80178%Z, a80178 (* tbnz w1, #5, 8018c <uart1_putc+0x24> *));
  (0x8017c%Z, a8017c (* nop *));
  (0x80180%Z, a80180 (* nop *));
  (0x80184%Z, a80184 (* ldr w1, [x2] *));
  (0x80188%Z, a80188 (* tbz w1, #5, 80180 <uart1_putc+0x18> *));
  (0x8018c%Z, a8018c (* mov x1, #0x5040 *));
  (0x80190%Z, a80190 (* movk x1, #0x3f21, lsl #16 *));
  (0x80194%Z, a80194 (* str w0, [x1] *));
  (0x80198%Z, a80198 (* ret *));
  (0x8019c%Z, a8019c (* nop *))
].
