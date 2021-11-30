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
From isla.instructions.rbit Require Import instrs.

(*PROOF_START*)
Lemma simplify_stuff (b n : bv 64) :
  bv_extract 0 1 (bv_shiftr b n) = bool_to_bv 1 (Z.testbit (bv_unsigned b) (bv_unsigned n)).
Proof. bv_simplify. bitblast as i. f_equal. lia. Qed.

Lemma simplify_more {N} (b : bv N) (n k : Z):
  0 ≤ n →
  0 ≤ k →
  k + n = Z.of_N N - 1 →
  bv_wrap N (bv_wrap N (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b) k))) ≪ n) =
  bool_to_Z (Z.testbit (bv_unsigned b) k) ≪ n.
Proof. move => ?? HN. bitblast as i. Qed.
(*PROOF_END*)

(*SPEC_START*)
Fixpoint rbit_Z_aux (N : nat) (z : Z) (n : nat) : Z :=
  match n with
  | O   => 0
  | S n => Z.lor (rbit_Z_aux N z n) ((bool_to_Z (Z.testbit z n)) ≪ (N - S n)%nat)
  end.

Definition rbit_Z N z := rbit_Z_aux N z N.
(*SPEC_END*)

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*SPEC_START*)
Definition rbit_spec (stack_size : Z) : iProp Σ := (
  c_call stack_size (λ args sp RET,
    ∃ (x : Z) P,
    ⌜bv_unsigned (args !!! 0%nat) = x⌝ ∗
    P ∗
    RET (λ rets,
      ⌜bv_unsigned (rets !!! 0%nat) = rbit_Z 64 x⌝ ∗
      P ∗
      True)
  )
)%I.
(*SPEC_END*)
Global Instance : LithiumUnfold (rbit_spec) := I.

Lemma rbit stack_size :
(*SPEC_START*)
  0 ≤ stack_size →
(*SPEC_END*)
  instr 0x0 (Some a0) -∗
  instr 0x4 (Some a4) -∗
  instr_body 0x0 (rbit_spec stack_size).
Proof.
(*PROOF_START*)
  move => ?. iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.

  rewrite !simplify_stuff. simpl.
  rewrite !bv_unsigned_BV. simpl.
  rewrite /rbit_Z /rbit_Z_aux /=.

  rewrite -(bv_wrap_idemp _ (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63)))).
  rewrite -(Z.shiftl_0_r (bv_wrap 64 (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63))))).
  repeat (rewrite simplify_more; [|lia|lia|lia]).
  rewrite /Z.of_nat /=.

  repeat match goal with
  | |- Z.lor _ _ = Z.lor _ _ => f_equal
  | |- Z.land (Z.land _ _) _ = _ => rewrite -Z.land_assoc
  | |- Z.land _ _ = _ => rewrite Z.land_lor_distr_l
  | |- _ = bool_to_Z _ ≪ _ => by destruct (Z.testbit _ _)
  end.

  vm_compute. by case_match.
(*PROOF_END*)
Time Qed.

End proof.
