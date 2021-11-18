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

Require Export isla.base.
Require Import iris.program_logic.adequacy.

Record module (EV : Type) := {
  m_state : Type;
  m_step : m_state → option EV → m_state → Prop;
  m_non_ub_state : m_state → Prop;
}.
Arguments m_state {_}.
Arguments m_step {_}.
Arguments m_non_ub_state {_}.

Inductive steps {EV} (m : module EV) : m.(m_state) → list EV → m.(m_state) → Prop :=
| steps_refl ρ :
  steps m ρ [] ρ
| steps_l ρ1 ρ2 ρ3 κ κs :
  m_step m ρ1 κ ρ2 →
  steps m ρ2 κs ρ3 →
  steps m ρ1 (option_list κ ++ κs) ρ3.

Definition safe {EV} (m : module EV) (σ : m.(m_state)) :=
  (∀ κs σ', steps m σ κs σ' → m_non_ub_state m σ').

Definition refines {EV} (m1 : module EV) (σ1 : m1.(m_state)) (m2 : module EV) (σ2 : m2.(m_state)) :=
  safe m2 σ2 →
  ∀ κs σ1', steps m1 σ1 κs σ1' → ∃ σ2', steps m2 σ2 κs σ2' ∧ m_non_ub_state m1 σ1'.

(*** Lemmas *)
Lemma steps_l' {EV} (m : module EV) ρ1 ρ2 ρ3 κ κs κs' :
  m_step m ρ1 κ ρ2 →
  steps m ρ2 κs ρ3 →
  κs' = option_list κ ++ κs →
  steps m ρ1 κs' ρ3.
Proof. move => ?? ->. by econstructor. Qed.

Lemma steps_trans {EV} κs1 κs2 (m : module EV) σ1 σ2 σ3 :
  steps m σ1 κs1 σ2 →
  steps m σ2 κs2 σ3 →
  steps m σ1 (κs1 ++ κs2) σ3.
Proof.
  elim.
  - naive_solver.
  - move => ?????????. rewrite -app_assoc. econstructor; eauto.
Qed.

Lemma safe_steps {EV} κs (m : module EV) σ1 σ2 :
  safe m σ1 →
  steps m σ1 κs σ2 →
  safe m σ2.
Proof. move => Hsafe Hsteps ???. apply: Hsafe. by apply: steps_trans. Qed.

Lemma refines_preserves_safe {EV} (m1 m2 : module EV) σ1 σ2:
  safe m2 σ2 →
  refines m1 σ1 m2 σ2 →
  safe m1 σ1.
Proof. move => Hsafe Hrefines κs σ1' Hsteps. unfold refines in *. naive_solver. Qed.

(*** [raw_sim]: Simulation *)
Inductive raw_sim {EV} (mi ms : module EV) : nat → mi.(m_state) → ms.(m_state) → Prop :=
| RawSimStep n σi1 σs1:
  (safe ms σs1 → m_non_ub_state mi σi1 ∧
  (∀ σi2 κ n', n = S n' → m_step mi σi1 κ σi2 ->
    ∃ σs2, steps ms σs1 (option_list κ) σs2 ∧ raw_sim mi ms n' σi2 σs2)) ->
  raw_sim mi ms n σi1 σs1.

Lemma m_forall_to_ex A B (P : A → B → Prop) (Q : B → Prop):
 (∃ n : A, ∀ y : B, P n y → Q y) -> ∀ y : B, ((∀ n : A, P n y) → Q y).
Proof. naive_solver. Qed.

Lemma raw_sim_implies_refines {EV} (mi ms : module EV) σi σs:
  (∀ n, raw_sim mi ms n σi σs) →
  refines mi σi ms σs.
Proof.
  move => Hsim Hsafe κs σi' Hsteps.
  move: σs Hsim Hsafe. apply: m_forall_to_ex.
  elim: Hsteps => {σi κs}.
  - move => σi1. eexists 0%nat => σs1 Hsim Hsafe. eexists _. split; [ by apply: steps_refl|].
    inversion Hsim; naive_solver.
  - move => σi1 σi2 σi3 κ κs Hstep Hsteps [n IH]. eexists (S n) => σs1 Hwp Hsafe.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have [|? Hwp]:= Hwp2 => //.
    have [|?[? Hsim]]:= (Hwp _ _ n _ ltac:(done)) => //.
    have [|?[??]]:= IH _ ltac:(done). { by apply: safe_steps. }
    eexists _. split; [|done]. by apply: steps_trans.
Qed.

Lemma raw_sim_safe {EV} (mi ms : module EV) σi σs n:
  (safe ms σs → raw_sim mi ms n σi σs) →
  raw_sim mi ms n σi σs.
Proof. move => Hsim. constructor => Hsafe. move: (Hsim Hsafe) => {}Hsim. inversion Hsim; naive_solver. Qed.

Lemma raw_sim_step_i {EV} (mi ms : module EV) σi σs n:
  m_non_ub_state mi σi →
  (∀ σi2 κ n', n = S n' → m_step mi σi κ σi2 ->
    κ = None ∧ raw_sim mi ms n' σi2 σs) →
  raw_sim mi ms n σi σs.
Proof.
  move => ? Hsim. constructor => Hsafe. split; [done|].
  move => σi2 κ n' ??.
  have [??]:= Hsim _ _ _ ltac:(done) ltac:(done). subst.
  eexists _. split; [|done]. apply: steps_refl.
Qed.

Lemma raw_sim_step_s {EV} (mi ms : module EV) σi σs σs' n:
  m_step ms σs None σs' →
  raw_sim mi ms n σi σs' →
  raw_sim mi ms n σi σs.
Proof.
  move => ? Hsim. constructor => Hsafe. inversion Hsim as [??? Hsim2]; simplify_eq.
  have [|? {}Hsim]:= Hsim2. { apply: safe_steps; [done|]. apply: steps_l; [done|]. apply: steps_refl. }
  split; [done|]. move => ?????.
  have [?[??]]:= Hsim _ _ _ ltac:(done) ltac:(done).
  eexists _. split; [|done]. by apply: steps_l'.
Qed.

(*** Iris module *)
Inductive iris_step (Λ : language) : (expr Λ * state Λ) → option (observation Λ) → (expr Λ * state Λ) → Prop :=
| IStep e σ κ e' σ':
  prim_step e σ (option_list κ) e' σ' [] →
  iris_step Λ (e, σ) κ (e', σ').

Definition iris_module (Λ : language) : module (Λ.(observation)) := {|
  m_step := (iris_step Λ);
  m_non_ub_state σ := not_stuck σ.1 σ.2;
|}.

Definition iris_module_wf (Λ : language) : Prop :=
  ∀ e σ κs e' σ' efs, prim_step (l := Λ) e σ κs e' σ' efs → (length κs ≤ 1)%nat ∧ efs = [].

Lemma nsteps_steps (Λ : language) σ κs σ' :
  iris_module_wf Λ →
  steps (iris_module Λ) σ κs σ' ↔ ∃ n, nsteps n ([σ.1], σ.2) κs ([σ'.1], σ'.2).
Proof.
  move => Hwf.
  split.
  - elim.
    + move => ?. eexists 0. constructor.
    + move => ????? Hstep _ [n Hsteps]. inversion Hstep; simplify_eq/=.
      eexists (S n). econstructor; [|done].
      by apply: (step_atomic _ _ _ _ _ [] []); [| |done].
  - move => [n]. elim: n σ κs σ'.
    + move => σ κs σ'. inversion 1; simplify_eq. destruct σ, σ'; simplify_eq/=. by constructor.
    + move => n IH σ κs σ'.
      inversion 1; simplify_eq. rename select (step _ _ _) into Hstep.
      inversion Hstep; simplify_list_eq. destruct t1 as [|? t1]; simplify_list_eq. 2: { by destruct t1. }
      have [??]:= Hwf _ _ _ _ _ _ ltac:(done).
      have [??]: ∃ κ', κ = option_list κ'; subst.
      { destruct κ as [|κ' κ]; [by eexists None|]. destruct κ; simplify_eq/=; [ by eexists (Some _)| lia]. }
      apply: steps_l; [| by apply: (IH (_, _))].
      destruct σ. by constructor.
Qed.

Lemma iris_transfer_refines Λ e1 σ1 m σ Pκs:
  iris_module_wf Λ →
  (∀ κs n t2 σ2, nsteps n ([e1], σ1) κs (t2, σ2) → (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs) →
  refines m σ (iris_module Λ) (e1, σ1) →
  safe m σ ∧ (∀ κs σ', steps m σ κs σ' → Pκs κs).
Proof.
  move => Hwf Hsteps Hrefines.
  have Hsafe : safe (iris_module Λ) (e1, σ1).
  { move => ?? /nsteps_steps[|/=??]; [done|]. have [Hs ?]:= Hsteps _ _ _ _ ltac:(done). apply: Hs. set_solver. }
  split; [ by apply: refines_preserves_safe|].
  move => ?? /Hrefines[|?[/nsteps_steps[|/=??]]]//?. naive_solver.
Qed.
