Require Import isla.isla_lang.
Require Export isla.examples.pkvm_handler.a7400.
Require Export isla.examples.pkvm_handler.a7400_spec.
Require Export isla.examples.pkvm_handler.a7404.
Require Export isla.examples.pkvm_handler.a7408.
Require Export isla.examples.pkvm_handler.a7408_spec.
Require Export isla.examples.pkvm_handler.a740c.
Require Export isla.examples.pkvm_handler.a740c_spec.
Require Export isla.examples.pkvm_handler.a7410.
Require Export isla.examples.pkvm_handler.a7414.
Require Export isla.examples.pkvm_handler.a7414_spec.
Require Export isla.examples.pkvm_handler.a7418.
Require Export isla.examples.pkvm_handler.a7418_spec.
Require Export isla.examples.pkvm_handler.a741c.
Require Export isla.examples.pkvm_handler.a7420.
Require Export isla.examples.pkvm_handler.a7424.
Require Export isla.examples.pkvm_handler.a7424_spec.
Require Export isla.examples.pkvm_handler.a7428.
Require Export isla.examples.pkvm_handler.a742c.
Require Export isla.examples.pkvm_handler.a7430.
Require Export isla.examples.pkvm_handler.a7434.
Require Export isla.examples.pkvm_handler.a7438.
Require Export isla.examples.pkvm_handler.a7438_spec.
Require Export isla.examples.pkvm_handler.a743c.
Require Export isla.examples.pkvm_handler.a18218.
Require Export isla.examples.pkvm_handler.a18218_spec.
Require Export isla.examples.pkvm_handler.a1821c.
Require Export isla.examples.pkvm_handler.a18220.
Require Export isla.examples.pkvm_handler.a18224.
Require Export isla.examples.pkvm_handler.a18228.
Require Export isla.examples.pkvm_handler.a1822c.
Require Export isla.examples.pkvm_handler.a18230.
Require Export isla.examples.pkvm_handler.a18234.
Require Export isla.examples.pkvm_handler.a18238.
Require Export isla.examples.pkvm_handler.a1823c.
Require Export isla.examples.pkvm_handler.a1823c_spec.
Require Export isla.examples.pkvm_handler.a18240.
Require Export isla.examples.pkvm_handler.a18244.
Require Export isla.examples.pkvm_handler.a18248.
Require Export isla.examples.pkvm_handler.a1824c.
Require Export isla.examples.pkvm_handler.a18250.
Require Export isla.examples.pkvm_handler.a18254.
Require Export isla.examples.pkvm_handler.a18258.
Require Export isla.examples.pkvm_handler.a1825c.
Require Export isla.examples.pkvm_handler.a18260.
Require Export isla.examples.pkvm_handler.a18264.
Require Export isla.examples.pkvm_handler.a18268.
Require Export isla.examples.pkvm_handler.a1826c.
Require Export isla.examples.pkvm_handler.a18270.
Require Export isla.examples.pkvm_handler.a18274.
Require Export isla.examples.pkvm_handler.a18278.
Require Export isla.examples.pkvm_handler.a1827c.
Require Export isla.examples.pkvm_handler.a18280.
Require Export isla.examples.pkvm_handler.a18284.
Require Export isla.examples.pkvm_handler.a18288.
Require Export isla.examples.pkvm_handler.a1828c.
Require Export isla.examples.pkvm_handler.a18290.

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
  (0x743c%Z, a743c (* br x5 *));
  (0x18218%Z, a18218 (* cmp x0, #0x1 *));
  (0x1821c%Z, a1821c (* b.ne 1823c <__kvm_handle_stub_hvc+0x24> *));
  (0x18220%Z, a18220 (* msr elr_el2, x1 *));
  (0x18224%Z, a18224 (* mov x0, #0x3c9 *));
  (0x18228%Z, a18228 (* msr spsr_el2, x0 *));
  (0x1822c%Z, a1822c (* mov x0, x2 *));
  (0x18230%Z, a18230 (* mov x1, x3 *));
  (0x18234%Z, a18234 (* mov x2, x4 *));
  (0x18238%Z, a18238 (* b 18248 <reset> *));
  (0x1823c%Z, a1823c (* cmp x0, #0x2 *));
  (0x18240%Z, a18240 (* b.ne 18288 <reset+0x40> *));
  (0x18244%Z, a18244 (* mov x0, xzr *));
  (0x18248%Z, a18248 (* mrs x5, sctlr_el2 *));
  (0x1824c%Z, a1824c (* mov x6, #0x200000 *));
  (0x18250%Z, a18250 (* movk x6, #0x100f *));
  (0x18254%Z, a18254 (* bic x5, x5, x6 *));
  (0x18258%Z, a18258 (* isb *));
  (0x1825c%Z, a1825c (* msr sctlr_el2, x5 *));
  (0x18260%Z, a18260 (* isb *));
  (0x18264%Z, a18264 (* nop *));
  (0x18268%Z, a18268 (* nop *));
  (0x1826c%Z, a1826c (* nop *));
  (0x18270%Z, a18270 (* nop *));
  (0x18274%Z, a18274 (* nop *));
  (0x18278%Z, a18278 (* adrp x5, 1c000 <hyp_memory+0x450> *));
  (0x1827c%Z, a1827c (* add x5, x5, #0x798 *));
  (0x18280%Z, a18280 (* msr vbar_el2, x5 *));
  (0x18284%Z, a18284 (* eret *));
  (0x18288%Z, a18288 (* mov x0, #0xbad0000 *));
  (0x1828c%Z, a1828c (* movk x0, #0xca11 *));
  (0x18290%Z, a18290 (* eret *))
].
