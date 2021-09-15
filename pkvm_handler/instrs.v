From isla Require Import isla_lang.
Require Export isla.examples.pkvm_handler.a7400.
Require Export isla.examples.pkvm_handler.a7404.
Require Export isla.examples.pkvm_handler.a7408.
Require Export isla.examples.pkvm_handler.a740c.
Require Export isla.examples.pkvm_handler.a7410.
Require Export isla.examples.pkvm_handler.a7414.
Require Export isla.examples.pkvm_handler.a7418.
Require Export isla.examples.pkvm_handler.a741c.
Require Export isla.examples.pkvm_handler.a7420.
Require Export isla.examples.pkvm_handler.a7424.
Require Export isla.examples.pkvm_handler.a7428.
Require Export isla.examples.pkvm_handler.a742c.
Require Export isla.examples.pkvm_handler.a7430.
Require Export isla.examples.pkvm_handler.a7434.
Require Export isla.examples.pkvm_handler.a7438.
Require Export isla.examples.pkvm_handler.a743c.

Definition instr_map := [
  (0x7400%Z, a7400 (* stp x0, x1, [sp, #-16]! *));
  (0x7404%Z, a7404 (* mrs x0, esr_el2 *));
  (0x7408%Z, a7408 (* lsr x0, x0, #26 *));
  (0x740c%Z, a740c (* cmp x0, #0x16 *));
  (0x7410%Z, a7410 (* b.ne 6800 <__host_exit> *));
  (0x7414%Z, a7414 (* ldp x0, x1, [sp] *));
  (0x7418%Z, a7418 (* cmp x0, #0x3 *));
  (0x741c%Z, a741c (* b.cs 6800 <__host_exit> *));
  (0x7420%Z, a7420 (* add sp, sp, #0x10 *));
  (0x7424%Z, a7424 (* ldr x5, 77f8 <__kvm_hyp_host_forward_smc+0x64> *));
  (0x7428%Z, a7428 (* mov x6, #0x0 *));
  (0x742c%Z, a742c (* movk x6, #0x0, lsl #16 *));
  (0x7430%Z, a7430 (* movk x6, #0x0, lsl #32 *));
  (0x7434%Z, a7434 (* movk x6, #0x0, lsl #48 *));
  (0x7438%Z, a7438 (* sub x5, x5, x6 *));
  (0x743c%Z, a743c (* br x5 *))
].
