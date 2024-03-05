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

(* This file tests that Ite and Manyop And work correctly (to test
that an issue reported by Ricardo Almeida has been fixed). *)

Definition instr_ite : isla_trace :=
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R2" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DefineConst 3%Z (Ite (Manyop And [
     Binop Eq (Val (Val_Symbolic 1%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0%Z)) Mk_annot) Mk_annot;
     Binop Eq (Val (Val_Symbolic 2%Z) Mk_annot) (Val (Val_Bits (BV 64%N 1%Z)) Mk_annot) Mk_annot
                               ] Mk_annot)
                          (Val (Val_Bits (BV 64%N 0%Z)) Mk_annot)
                          (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DeclareConst 10%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 10%Z)) Mk_annot :t:
  Smt (DefineConst 11%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 10%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 11%Z)) Mk_annot :t:
  tnil
.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  ∃ (v1 v2 vold : bv 64),
  "R1" ↦ᵣ RVal_Bits v1 ∗
  "R2" ↦ᵣ RVal_Bits v2 ∗
  "R0" ↦ᵣ RVal_Bits vold ∗
  instr_pre a (
    "R1" ↦ᵣ RVal_Bits v1 ∗
    "R2" ↦ᵣ RVal_Bits v2 ∗
    "R0" ↦ᵣ RVal_Bits (ite (bool_decide (v1 = 0%bv) && bool_decide (v2 = 1%bv)) 0%bv v1) ∗
    True).

Lemma ite_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some instr_ite) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
