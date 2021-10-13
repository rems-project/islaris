Require Import isla.aarch64.aarch64.
From isla.instructions.uart Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Notation bus_to_reg32 b := (b - 0x3f000000) (only parsing).
Definition AUX_MU_LSR_REG : addr := [BV{64} bus_to_reg32 0x7e215054].
Definition AUX_MU_IO_REG : addr := [BV{64} bus_to_reg32 0x7e215040].

Definition spec_uart_wait_write_body (P R : spec) : spec :=
  sexists (λ b : bv 32, scons (SReadMem AUX_MU_LSR_REG b)
                              (sif (Z.testbit (bv_unsigned b) 5 = true) P R)).
Global Instance spec_uart_wait_write_body_mono P :
  MonoPred (spec_uart_wait_write_body P).
Proof. constructor. unfold spec_uart_wait_write_body. by unshelve spec_solver. Qed.

Definition spec_uart_wait_write (P : spec) : spec :=
  srec (spec_uart_wait_write_body P).

Definition spec_uart_write (c : bv 32) (P : spec) : spec :=
  spec_uart_wait_write (scons (SWriteMem AUX_MU_IO_REG c) P).

Definition uart1_putc_loop_spec : iProp Σ :=
  ∃ P,
  "R1" ↦ᵣ: λ _,
  "R2" ↦ᵣ RVal_Bits AUX_MU_LSR_REG ∗
  mmio_range AUX_MU_LSR_REG 0x4 ∗
  reg_col sys_regs ∗
  spec_trace (spec_uart_wait_write P) ∗
  instr_pre 0x000000000008018c (
    ∃ r1,
    "R1" ↦ᵣ RVal_Bits r1 ∗
    "R2" ↦ᵣ RVal_Bits AUX_MU_LSR_REG ∗
    reg_col sys_regs ∗
    spec_trace P ∗
    True
  )
.
Global Instance : LithiumUnfold (uart1_putc_loop_spec) := I.

Lemma uart1_putc_loop :
  instr 0x0000000000080180 (Some a80180) -∗
  instr 0x0000000000080184 (Some a80184) -∗
  instr 0x0000000000080188 (Some a80188) -∗
  □ instr_pre 0x0000000000080180 uart1_putc_loop_spec -∗
  instr_body 0x0000000000080180 uart1_putc_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar P.
  Time repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  - bv_solve.
  - rename select (_ ≠ _) into Hn.
    rewrite sif_true; [done|]. apply not_false_is_true.
    contradict Hn. bits_simplify. have -> : n1 = 0 by lia. done.
  - rename select (_ = _) into Hn.
    rewrite sif_false; [done|]. apply not_true_iff_false.
    bitify_hyp Hn. move: (Hn 0 ltac:(done)) => {}Hn.
    by bits_simplify_hyp Hn.
Time Qed.

Definition uart1_putc_spec : iProp Σ :=
  ∃ P (c ret : bv 64),
  "R0" ↦ᵣ RVal_Bits c ∗
  "R1" ↦ᵣ: λ _,
  "R2" ↦ᵣ: λ _,
  "R30" ↦ᵣ RVal_Bits ret ∗
  mmio_range AUX_MU_LSR_REG 0x4 ∗
  mmio_range AUX_MU_IO_REG 0x4 ∗
  reg_col sys_regs ∗
  spec_trace (spec_uart_write (bv_zero_extend 32 (bv_extract 0 8 c)) P) ∗
  instr_pre (bv_unsigned ret) (
    ∃ r0 r1 r2 : bv 64,
    "R0" ↦ᵣ RVal_Bits r0 ∗
    "R1" ↦ᵣ RVal_Bits r1 ∗
    "R2" ↦ᵣ RVal_Bits r2 ∗
    reg_col sys_regs ∗
    spec_trace P ∗
    True
  )
.
Global Instance : LithiumUnfold (uart1_putc_spec) := I.

Lemma uart1_putc :
  instr 0x0000000000080168 (Some a80168) -∗
  instr 0x000000000008016c (Some a8016c) -∗
  instr 0x0000000000080170 (Some a80170) -∗
  instr 0x0000000000080174 (Some a80174) -∗
  instr 0x0000000000080178 (Some a80178) -∗
  instr 0x000000000008017c (Some a8017c) -∗
  □ instr_pre 0x0000000000080180 uart1_putc_loop_spec -∗
  instr 0x000000000008018c (Some a8018c) -∗
  instr 0x0000000000080190 (Some a80190) -∗
  instr 0x0000000000080194 (Some a80194) -∗
  instr 0x0000000000080198 (Some a80198) -∗

  instr_body 0x0000000000080168 (uart1_putc_spec).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  - rewrite sif_false; [|li_shelve_sidecond].
    liInst Hevar (scons (SWriteMem AUX_MU_IO_REG (bv_zero_extend 32 (bv_extract 0 8 c))) P).
    Time repeat liAStep; liShow.
  - rewrite sif_true; [|li_shelve_sidecond].
    Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try by bv_solve.
  all: try by bits_simplify.
  + rename select (_ ≠ [BV{1} 1]) into Hn. contradict Hn. bits_simplify.
    by have -> : n1 = 0 by lia.
  + rename select (_ = [BV{1} 1]) into Hn.
    bitify_hyp Hn. move: (Hn 0 ltac:(done)) => {}Hn.
    by bits_simplify_hyp Hn.
Time Qed.
End proof.
