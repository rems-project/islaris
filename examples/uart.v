(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import isla.aarch64.aarch64.
From isla.instructions.uart Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*SPEC_START*)
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
(*SPEC_END*)

(*PROOF_START*)
Definition uart1_putc_loop_spec : iProp Σ :=
  ∃ P,
  "R1" ↦ᵣ: λ _,
  "R2" ↦ᵣ RVal_Bits AUX_MU_LSR_REG ∗
  mmio_range (bv_unsigned AUX_MU_LSR_REG) 0x4 ∗
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
(*PROOF_END*)
Global Instance : LithiumUnfold (uart1_putc_loop_spec) := I.

Lemma uart1_putc_loop :
  instr 0x0000000000080180 (Some a80180) -∗
  instr 0x0000000000080184 (Some a80184) -∗
  instr 0x0000000000080188 (Some a80188) -∗
  □ instr_pre 0x0000000000080180 uart1_putc_loop_spec -∗
  instr_body 0x0000000000080180 uart1_putc_loop_spec.
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  liInst Hevar P.
  liARun.

  Unshelve. all: prepare_sidecond.
  - bv_solve.
  - rename select (_ ≠ _) into Hn.
    rewrite sif_true; [done|]. apply not_false_is_true.
    contradict Hn. bv_simplify. bitblast as i. by have -> : i = 0 by lia.
  - rename select (_ = _) into Hn.
    rewrite sif_false; [done|]. apply not_true_iff_false.
    bv_simplify Hn. by bitblast Hn with 0.
(*PROOF_END*)
Time Qed.

(*SPEC_START*)
Definition uart1_putc_spec : iProp Σ :=
  ∃ P (c ret : bv 64),
  "R0" ↦ᵣ RVal_Bits c ∗
  "R1" ↦ᵣ: λ _,
  "R2" ↦ᵣ: λ _,
  "R30" ↦ᵣ RVal_Bits ret ∗
  mmio_range (bv_unsigned AUX_MU_LSR_REG) 0x4 ∗
  mmio_range (bv_unsigned AUX_MU_IO_REG) 0x4 ∗
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
(*SPEC_END*)
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
(*PROOF_START*)
  iStartProof.
  liARun.
  - rewrite sif_true; [|li_shelve_sidecond].
    liARun.
  - rewrite sif_false; [|li_shelve_sidecond].
    liInst Hevar (scons (SWriteMem AUX_MU_IO_REG (bv_zero_extend 32 (bv_extract 0 8 c))) P).
    liARun.
  Unshelve. all: prepare_sidecond.
  all: try by bv_solve.
  all: try by bv_simplify; bitblast.
  + rename select (_ = [BV{1} 1]) into Hn.
    bv_simplify Hn. by bitblast Hn with 0.
  + rename select (_ ≠ [BV{1} 1]) into Hn. contradict Hn. bv_simplify. bitblast as i.
    by have -> : i = 0 by lia.
(*PROOF_END*)
Time Qed.
End proof.
