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

Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.riscv64.arch.
Require Import isla.riscv64.sys_regs.

Definition tmp_registers : list string :=
  ["x5"; "x6"; "x7"; "x28"; "x29"; "x30"; "x31"].

Definition c_call_ret `{!islaG Σ} `{!threadG} (stack_size : Z) (regs : list valu) (ret sp : bv 64) (Q : (list (bv 64) → iProp Σ)) : iProp Σ :=
  reg_col sys_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> (["x1"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++ tmp_registers)) ∗
  reg_col (zip_with (λ r v, (KindReg r, ExactShape v)) ["x8"; "x9"; "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"] regs) ∗
  "x10" ↦ᵣ: λ r10, ∃ b10 : bv 64, ⌜r10 = RVal_Bits b10⌝ ∗
  "x11" ↦ᵣ: λ r11, ∃ b11 : bv 64, ⌜r11 = RVal_Bits b11⌝ ∗
  "x2" ↦ᵣ RVal_Bits sp ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  Q [b10; b11].
Global Instance : LithiumUnfold (@c_call_ret) := I.


Definition c_call `{!islaG Σ} `{!threadG} (stack_size : Z) (P : list (bv 64) → bv 64 → ((list (bv 64) → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ (sp ret : bv 64),
  reg_col sys_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
  "x10" ↦ᵣ: λ r10, ∃ b10 : bv 64, ⌜r10 = RVal_Bits b10⌝ ∗
  "x11" ↦ᵣ: λ r11, ∃ b11 : bv 64, ⌜r11 = RVal_Bits b11⌝ ∗
  "x12" ↦ᵣ: λ r12, ∃ b12 : bv 64, ⌜r12 = RVal_Bits b12⌝ ∗
  "x13" ↦ᵣ: λ r13, ∃ b13 : bv 64, ⌜r13 = RVal_Bits b13⌝ ∗
  "x14" ↦ᵣ: λ r14, ∃ b14 : bv 64, ⌜r14 = RVal_Bits b14⌝ ∗
  "x15" ↦ᵣ: λ r15, ∃ b15 : bv 64, ⌜r15 = RVal_Bits b15⌝ ∗
  "x16" ↦ᵣ: λ r16, ∃ b16 : bv 64, ⌜r16 = RVal_Bits b16⌝ ∗
  "x17" ↦ᵣ: λ r17, ∃ b17 : bv 64, ⌜r17 = RVal_Bits b17⌝ ∗
  "x8" ↦ᵣ: λ r8, ⌜valu_has_shape r8 (BitsShape 64)⌝ ∗
  "x9" ↦ᵣ: λ r9, ⌜valu_has_shape r9 (BitsShape 64)⌝ ∗
  "x18" ↦ᵣ: λ r18, ⌜valu_has_shape r18 (BitsShape 64)⌝ ∗
  "x19" ↦ᵣ: λ r19, ⌜valu_has_shape r19 (BitsShape 64)⌝ ∗
  "x20" ↦ᵣ: λ r20, ⌜valu_has_shape r20 (BitsShape 64)⌝ ∗
  "x21" ↦ᵣ: λ r21, ⌜valu_has_shape r21 (BitsShape 64)⌝ ∗
  "x22" ↦ᵣ: λ r22, ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
  "x23" ↦ᵣ: λ r23, ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
  "x24" ↦ᵣ: λ r24, ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
  "x25" ↦ᵣ: λ r25, ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "x26" ↦ᵣ: λ r26, ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "x27" ↦ᵣ: λ r27, ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "x1" ↦ᵣ RVal_Bits ret ∗
  "x2" ↦ᵣ RVal_Bits sp ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜bv_extract 0 1 ret = (BV 1 0)⌝ ∗ ⌜bv_extract 1 1 ret = (BV 1 0)⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned sp - stack_size ∧ bv_unsigned sp < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  P [b10; b11; b12; b13; b14; b15; b16; b17] sp (λ Q,
  instr_pre (bv_unsigned ret) (
      c_call_ret stack_size [r8; r9; r18; r19; r20; r21; r22; r23; r24; r25; r26; r27] ret sp Q
  )).
Global Instance : LithiumUnfold (@c_call) := I.
