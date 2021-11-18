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
(* This was in part funded from the European Research Council (ERC) under   *)
(* the European Union's Horizon 2020 research and innovation programme      *)
(* (grant agreement No 789108, "ELVER"), in part supported by the UK        *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), and in part funded by Google.           *)
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
Require Import isla.instructions.instr_stp.

Definition spec `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
  ∃ (vold1 vold2 : bv 64),
  "R0" ↦ᵣ RVal_Bits v1 ∗
  "R1" ↦ᵣ RVal_Bits v2 ∗
  (bv_unsigned sp - 16) ↦ₘ vold1 ∗
  (bv_unsigned sp - 8) ↦ₘ vold2 ∗
  ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
  ⌜16 < bv_unsigned sp < 2 ^ 52⌝ ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R0" ↦ᵣ RVal_Bits v1 ∗
    "R1" ↦ᵣ RVal_Bits v2 ∗
    "SP_EL2" ↦ᵣ RVal_Bits (bv_sub sp [BV{64} 16])∗
    reg_col sys_regs ∗
    (bv_unsigned sp - 16) ↦ₘ v1 ∗
    (bv_unsigned sp - 8) ↦ₘ v2 ∗
    True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64):
  instr 0x0000000010300000 (Some instr_stp) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004 sp v1 v2).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.
