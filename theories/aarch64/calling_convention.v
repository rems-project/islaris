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

Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.aarch64.arch.
Require Import isla.aarch64.sys_regs.

Definition tmp_registers : list string :=
  ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"].

Definition c_call_ret `{!islaG Σ} `{!threadG} (stack_size : Z) (regs : list valu) (ret sp : bv 64) (Q : (list (bv 64) → iProp Σ)) : iProp Σ :=
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  reg_col (zip_with (λ r v, (KindReg r, ExactShape v)) ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"] regs) ∗
  "R0" ↦ᵣ: λ r0, ∃ b0 : bv 64, ⌜r0 = RVal_Bits b0⌝ ∗
  "R1" ↦ᵣ: λ r1, ∃ b1 : bv 64, ⌜r1 = RVal_Bits b1⌝ ∗
  "R2" ↦ᵣ: λ r2, ∃ b2 : bv 64, ⌜r2 = RVal_Bits b2⌝ ∗
  "R3" ↦ᵣ: λ r3, ∃ b3 : bv 64, ⌜r3 = RVal_Bits b3⌝ ∗
  "R4" ↦ᵣ: λ r4, ∃ b4 : bv 64, ⌜r4 = RVal_Bits b4⌝ ∗
  "R5" ↦ᵣ: λ r5, ∃ b5 : bv 64, ⌜r5 = RVal_Bits b5⌝ ∗
  "R6" ↦ᵣ: λ r6, ∃ b6 : bv 64, ⌜r6 = RVal_Bits b6⌝ ∗
  "R7" ↦ᵣ: λ r7, ∃ b7 : bv 64, ⌜r7 = RVal_Bits b7⌝ ∗
  "R8" ↦ᵣ: λ r8, ∃ b8 : bv 64, ⌜r8 = RVal_Bits b8⌝ ∗
  "R30" ↦ᵣ RVal_Bits ret ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  Q [b0; b1; b2; b3; b4; b5; b6; b7; b8].
Global Instance : LithiumUnfold (@c_call_ret) := I.


Definition c_call `{!islaG Σ} `{!threadG} (stack_size : Z) (P : list (bv 64) → bv 64 → ((list (bv 64) → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ (sp ret : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "R0" ↦ᵣ: λ r0, ∃ b0 : bv 64, ⌜r0 = RVal_Bits b0⌝ ∗
  "R1" ↦ᵣ: λ r1, ∃ b1 : bv 64, ⌜r1 = RVal_Bits b1⌝ ∗
  "R2" ↦ᵣ: λ r2, ∃ b2 : bv 64, ⌜r2 = RVal_Bits b2⌝ ∗
  "R3" ↦ᵣ: λ r3, ∃ b3 : bv 64, ⌜r3 = RVal_Bits b3⌝ ∗
  "R4" ↦ᵣ: λ r4, ∃ b4 : bv 64, ⌜r4 = RVal_Bits b4⌝ ∗
  "R5" ↦ᵣ: λ r5, ∃ b5 : bv 64, ⌜r5 = RVal_Bits b5⌝ ∗
  "R6" ↦ᵣ: λ r6, ∃ b6 : bv 64, ⌜r6 = RVal_Bits b6⌝ ∗
  "R7" ↦ᵣ: λ r7, ∃ b7 : bv 64, ⌜r7 = RVal_Bits b7⌝ ∗
  "R8" ↦ᵣ: λ r8, ⌜valu_has_shape r8 (BitsShape 64)⌝ ∗
  "R19" ↦ᵣ: λ r19, ⌜valu_has_shape r19 (BitsShape 64)⌝ ∗
  "R20" ↦ᵣ: λ r20, ⌜valu_has_shape r20 (BitsShape 64)⌝ ∗
  "R21" ↦ᵣ: λ r21, ⌜valu_has_shape r21 (BitsShape 64)⌝ ∗
  "R22" ↦ᵣ: λ r22, ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
  "R23" ↦ᵣ: λ r23, ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
  "R24" ↦ᵣ: λ r24, ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
  "R25" ↦ᵣ: λ r25, ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "R26" ↦ᵣ: λ r26, ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "R27" ↦ᵣ: λ r27, ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "R28" ↦ᵣ: λ r28, ⌜valu_has_shape r28 (BitsShape 64)⌝ ∗
  "R29" ↦ᵣ: λ r29, ⌜valu_has_shape r29 (BitsShape 64)⌝ ∗
  "R30" ↦ᵣ RVal_Bits ret ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  ⌜stack_size < bv_unsigned sp < 2 ^ 52⌝ ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  P [b0; b1; b2; b3; b4; b5; b6; b7] sp (λ Q,
  instr_pre (bv_unsigned ret) (
      c_call_ret stack_size [r19; r20; r21; r22; r23; r24; r25; r26; r27; r28; r29] ret sp Q
  )).
Global Instance : LithiumUnfold (@c_call) := I.
