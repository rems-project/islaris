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

Require Import lithium.pure_definitions.
Require Import lithium.simpl_classes.
Require Import isla.opsem.

Definition spec := list seq_label → Prop.

Global Instance spec_subseteq : SubsetEq spec := λ P1 P2, ∀ κs, P1 κs → P2 κs.
Global Instance spec_equiv : Equiv spec := λ P1 P2, ∀ κs, P1 κs ↔ P2 κs.

Canonical Structure specO := list seq_label -d> PropO.

Definition snil : spec :=
  λ κs, κs = [].

Definition scons (l : seq_label) (P : spec) : spec :=
  λ κs, κs = [] ∨ ∃ κs', κs = l::κs' ∧ (κs' = [] ∨ P κs').

Definition sapp (ls : list seq_label) (P : spec) : spec :=
  foldr scons P ls.

Definition sexists {A} (P : A → spec) : spec :=
  λ κs, ∃ a, P a κs.

Definition sif (C : Prop) (P1 : spec) (P2 : spec) : spec :=
  λ κs, (C ∧ P1 κs) ∨ (¬ C ∧ P2 κs).

Definition srec (P : spec → spec) : spec :=
  least_fixpoint P.

Ltac spec_unfold :=
  unfold subseteq, spec_subseteq, equiv, spec_equiv, scons, snil, sexists, sif in *.
Ltac spec_solver := spec_unfold; naive_solver.

Global Instance spec_equiv_equiv : Equivalence (≡@{spec}).
Proof. constructor => ? *; spec_solver. Qed.
Global Instance spec_subseteq_preorder : PreOrder (⊆@{spec}).
Proof. constructor => ? *; spec_solver. Qed.
Global Instance spec_subseteq_equiv_proper : Proper (equiv ==> equiv ==> iff) (⊆@{spec}).
Proof. move => ??????. spec_solver. Qed.

Lemma sif_true (P : Prop) Pκs1 Pκs2: P → sif P Pκs1 Pκs2 ≡ Pκs1.
Proof. spec_solver. Qed.
Lemma sif_false (P : Prop) Pκs1 Pκs2: ¬ P → sif P Pκs1 Pκs2 ≡ Pκs2.
Proof. spec_solver. Qed.


(* This is unsafe due to the κs' = [] ∨ ... in scons. *)
Global Instance simpl_and_scons_subseteq κ1 κ2 Pκs1 Pκs2:
  SimplAndUnsafe true (scons κ1 Pκs1 ⊆ scons κ2 Pκs2) (λ T, κ1 = κ2 ∧ Pκs1 ⊆ Pκs2 ∧ T).
Proof. move => ?. spec_solver. Qed.

(* Unsafe since there might be multiple different choices for x for different traces. *)
Global Instance simpl_and_scons_subseteq_sexists {A} κ1 Pκs1 Pκs2:
  SimplAndUnsafe true (scons κ1 Pκs1 ⊆ sexists Pκs2) (λ T, ∃ x : A, scons κ1 Pκs1 ⊆ Pκs2 x ∧ T).
Proof. move => ?. spec_solver. Qed.

Global Instance simpl_and_scons_subseteq_srec κ1 Pκs1 Prec `{!MonoPred Prec}:
  SimplAnd (scons κ1 Pκs1 ⊆ srec Prec) (λ T, scons κ1 Pκs1 ⊆ Prec (srec Prec) ∧ T).
Proof. split; move => [??]; (split; [|done]) => ??; apply/least_fixpoint_unfold; spec_solver. Qed.

Global Instance simpl_and_spec_subseteq_evar (Pκs1 Pκs2 : spec) `{!IsProtected Pκs1}:
  SimplAndUnsafe true (Pκs1 ⊆ Pκs2) (λ T, Pκs1 = Pκs2 ∧ T).
Proof. move => ?. spec_solver. Qed.
