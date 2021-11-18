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

Require Import isla.automation.
Require Import isla.riscv64.arch.
Require Import isla.riscv64.sys_regs.

Definition sd_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (offset : Z) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  (bv_unsigned r2 + offset) ↦ₘ? 8 ∗
  ⌜bv_unsigned r2 `mod` 8 = 0⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned r2 + offset < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    (bv_unsigned r2 + offset) ↦ₘ r1 ∗
    True
  ).
Global Instance : LithiumUnfold (@sd_spec) := I.

Definition ld_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (offset : Z) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ: λ _,
  R2 ↦ᵣ RVal_Bits r2 ∗
  (bv_unsigned r2 + offset) ↦ₘ r1 ∗
  ⌜bv_unsigned r2 `mod` 8 = 0⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned r2 + offset < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    (bv_unsigned r2 + offset) ↦ₘ r1 ∗
    True
  ).
Global Instance : LithiumUnfold (@ld_spec) := I.
