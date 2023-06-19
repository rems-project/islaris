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

Require Import isla.riscv64.riscv64.
From isla.instructions.memcpy_riscv64 Require Import instrs.

(*PROOF_START*)
Definition memcpy_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst n : bv 64) (srcdata dstdata : list byte) (i : nat),
  reg_col sys_regs ∗
  "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗ "x12" ↦ᵣ RVal_Bits n ∗
  "x13" ↦ᵣ RVal_Bits tmp ∗
  (bv_unsigned src - i) ↦ₘ∗ srcdata ∗ (bv_unsigned dst - i) ↦ₘ∗ dstdata ∗
  ⌜(bv_unsigned n + i)%Z = length srcdata⌝ ∗ ⌜(bv_unsigned n + i)%Z = length dstdata⌝ ∗
  ⌜0 < bv_unsigned n⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned dst ∧ bv_unsigned dst + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned src ∧ bv_unsigned src + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜take i dstdata = take i srcdata⌝ ∗
  instr_pre 0x000000001030001c (
    ∃ (tmp : bv 64),
      reg_col sys_regs ∗
      "x10" ↦ᵣ RVal_Bits (bv_add dst n) ∗
      "x11" ↦ᵣ RVal_Bits (bv_add src n) ∗ "x12" ↦ᵣ RVal_Bits (BV 64 0) ∗
      "x13" ↦ᵣ RVal_Bits tmp ∗
      (bv_unsigned src - i) ↦ₘ∗ srcdata ∗ (bv_unsigned dst - i) ↦ₘ∗ srcdata ∗
      True
  )
.
(*PROOF_END*)

Arguments memcpy_loop_spec /.

Lemma memcpy_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  □ instr_pre 0x0000000010300004 memcpy_loop_spec -∗
  instr_body 0x0000000010300004 memcpy_loop_spec.
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  liInst Hevar5 (S i).
  liARun.

  Unshelve. all: prepare_sidecond.
  all: try bv_simplify select (bv_add n _ = _).
  all: try bv_simplify select (bv_add n _ ≠ _).
  all: try rewrite insert_length.
  all: try bv_solve.
  - rewrite -(take_drop i (<[_ := _]> dstdata)).
    rewrite -(take_drop i srcdata).
    f_equal.
    + rewrite take_insert; [done|bv_solve].
    + erewrite drop_S. 2: { erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
      erewrite (drop_S srcdata). 2: { rewrite <- H10. f_equal. bv_solve. }
      rewrite !drop_ge ?insert_length //; [ |bv_solve..].
      f_equal. bv_solve.
  - erewrite take_S_r. 2: { erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
    erewrite take_S_r. 2: { rewrite <- H10. f_equal. bv_solve. }
    rewrite take_insert; [|bv_solve].
    f_equal; [done|]. f_equal. bv_solve.
(*PROOF_END*)
Time Qed.

Lemma memcpy `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300004 memcpy_loop_spec -∗
(*SPEC_START*)
  instr_body 0x0000000010300000 (
    ∃ (tmp src dst n ret : bv 64) (srcdata dstdata : list byte),
    reg_col sys_regs ∗
    "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗ "x12" ↦ᵣ RVal_Bits n ∗
    "x13" ↦ᵣ RVal_Bits tmp ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned dst ∧ bv_unsigned dst + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned src ∧ bv_unsigned src + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    ⌜bv_extract 0 1 ret = (BV 1 0)⌝ ∗ ⌜bv_extract 1 1 ret = (BV 1 0)⌝ ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp : bv 64),
      reg_col sys_regs ∗
      "x10" ↦ᵣ RVal_Bits (bv_add dst n) ∗ "x11" ↦ᵣ RVal_Bits (bv_add src n) ∗ "x12" ↦ᵣ RVal_Bits (BV 64 0) ∗
      "x13" ↦ᵣ RVal_Bits tmp ∗
      "x1" ↦ᵣ RVal_Bits ret ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
(*SPEC_END*)
  )).
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  liInst Hevar5 0%nat.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - by destruct dstdata, srcdata.
  - bv_simplify select (n ≠ _). bv_solve.
(*PROOF_END*)
Time Qed.
