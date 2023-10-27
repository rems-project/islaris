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

From Coq Require Export ssreflect.
From stdpp Require Export prelude strings gmap.
From stdpp.unstable Require Export bitblast.
From RecordUpdate Require Export RecordSet.
From iris.proofmode Require Import tactics.
From lithium Require Export base.
From stdpp.unstable Require Export bitvector.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Arguments set _ _ _ _ _ !_ /.

Arguments N.mul : simpl never.
Arguments bool_decide : simpl never.
Global Typeclasses Opaque prefix.

(* TODO: upstream? *)
Global Typeclasses Opaque Z.ge Z.le.

Ltac unLET :=
  repeat match goal with
         | H := _ |- _ => unfold H in *; clear H
         end.

Tactic Notation "case_match" "as" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.

Definition REMEMBER_MARK {A} (x y : A) : Prop := x = y.
Ltac remember_mark v :=
  let x := fresh "x" in
  let H := fresh "H" in
  pose (x := v);
  pattern v;
  lazymatch goal with
  | |- ?P _ => change_no_check (P x)
  end;
  pose proof (H := @eq_refl _ v);
  change (REMEMBER_MARK x v) in H;
  clearbody x;
  cbv beta.

Ltac subst_remembered :=
  repeat match goal with
         | H : REMEMBER_MARK ?x ?v |- _ =>
             change (x = v) in H;
             subst x
         end.

Lemma concat_join {A} (l : list (list A)):
  concat l = mjoin l.
Proof. by elim: l => // ??; csimpl => ->. Qed.
Lemma rev_reverse {A} (l : list A):
  rev l = reverse l.
Proof. elim: l => // ??/= ->. by rewrite reverse_cons. Qed.
Lemma map_fmap {A B} x (f : A → B):
  map f x = f <$> x.
Proof. done.  Qed.
Lemma option_map_fmap {A B} x (f : A → B):
  option_map f x = f <$> x.
Proof. by destruct x. Qed.

Lemma Zleb_bool_decide z1 z2:
  z1 <=? z2 = bool_decide (z1 ≤ z2).
Proof.
  case_bool_decide => //; try apply Zle_is_le_bool => //.
  destruct (z1 <=? z2) eqn: Hle => //. move: Hle => /Zle_is_le_bool.
  done.
Qed.

Lemma String_eqb_eq s1 s2:
  (s1 =? s2)%string = bool_decide (s1 = s2).
Proof. case_bool_decide; subst; by rewrite ?String.eqb_eq ?eqb_neq. Qed.

Lemma andb_bool_decide P1 P2 `{!Decision P1} `{!Decision P2} :
  bool_decide P1 && bool_decide P2 = bool_decide (P1 ∧ P2).
Proof. repeat case_bool_decide => //; naive_solver. Qed.

(* This has as better performance characteristic wrt. simpl compared
to list_find since list_find_idx does not contain prod_map. *)
Definition list_find_idx {A} P `{∀ x, Decision (P x)} : list A → option nat :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if decide (P x) then Some 0%nat else S <$> go l
  end.
Global Instance: Params (@list_find_idx) 3 := {}.

Section list_find_idx.
  Context {A} (P : A → Prop) `{∀ x, Decision (P x)}.

  Lemma list_find_idx_list_find l:
    list_find_idx P l = fst <$> list_find P l.
  Proof.
    elim: l => //= ?? ->. case_decide => //=.
    rewrite -!option_fmap_compose. by apply: option_fmap_ext.
  Qed.

  Lemma list_find_idx_Some l i:
    list_find_idx P l = Some i ↔
    ∃ x, l !! i = Some x ∧ P x ∧ ∀ j y, l !! j = Some y → (j < i)%nat → ¬P y.
  Proof.
    rewrite list_find_idx_list_find fmap_Some.
    split.
    - move => -[[??]]. rewrite list_find_Some. naive_solver.
    - move => [??]. eexists (_, _). rewrite list_find_Some. naive_solver.
  Qed.

  Lemma list_find_idx_lt l i:
    list_find_idx P l = Some i → (i < length l)%nat.
  Proof. move => /list_find_idx_Some[?[??]]. by apply: lookup_lt_Some. Qed.

  Lemma list_find_idx_insert_eq l i x:
    list_find_idx P l = Some i →
    P x →
    list_find_idx P (<[i:=x]> l) = Some i.
  Proof.
    rewrite !list_find_idx_Some => -[?[?[??]]] ?. eexists _.
    rewrite list_lookup_insert. 2: by apply: lookup_lt_Some. split_and! => //.
    move => ?? /list_lookup_insert_Some. naive_solver.
  Qed.

  Lemma list_find_idx_insert_neq l i j x y:
    list_find_idx P l = Some i →
    ¬ P x →
    l !! j = Some y →
    ¬ P y →
    list_find_idx P (<[j:=x]> l) = Some i.
  Proof.
    rewrite !list_find_idx_Some => -[?[?[??]]] ???. eexists _.
    rewrite list_lookup_insert_ne. 2: move => ?; by simplify_eq.
    split_and! => //. move => ?? /list_lookup_insert_Some. naive_solver.
  Qed.
End list_find_idx.

Definition list_find_idx_bool {A} (f : A → bool) : list A → option nat :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if f x then Some 0%nat else S <$> go l
  end.
Global Instance: Params (@list_find_idx_bool) 3 := {}.

Section list_find_idx_bool.
  Context {A} (f : A → bool).

  Lemma list_find_idx_bool_list_find_idx l:
    list_find_idx_bool f l = list_find_idx f l.
  Proof. elim: l => //= ?? ->. case_decide => //=; by case_match. Qed.

  Lemma list_find_idx_bool_Some l i:
    list_find_idx_bool f l = Some i ↔
    ∃ x, l !! i = Some x ∧ f x ∧ ∀ j y, l !! j = Some y → (j < i)%nat → ¬f y.
  Proof. by rewrite list_find_idx_bool_list_find_idx list_find_idx_Some. Qed.

  Lemma list_find_idx_bool_lt l i:
    list_find_idx_bool f l = Some i → (i < length l)%nat.
  Proof. move => /list_find_idx_bool_Some[?[??]]. by apply: lookup_lt_Some. Qed.

  Lemma list_find_idx_bool_insert_eq l i x:
    list_find_idx_bool f l = Some i →
    f x →
    list_find_idx_bool f (<[i:=x]> l) = Some i.
  Proof. rewrite !list_find_idx_bool_list_find_idx. apply: list_find_idx_insert_eq. Qed.

  Lemma list_find_idx_bool_insert_neq l i j x y:
    list_find_idx_bool f l = Some i →
    ¬ f x →
    l !! j = Some y →
    ¬ f y →
    list_find_idx_bool f (<[j:=x]> l) = Some i.
  Proof. rewrite !list_find_idx_bool_list_find_idx. apply: list_find_idx_insert_neq. Qed.
End list_find_idx_bool.

Definition list_find_bool {A} (f : A → bool) : list A → option (nat * A) :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if f x then Some (0%nat, x) else prod_map S id <$> go l
  end.
Global Instance: Params (@list_find_bool) 3 := {}.

Section list_find_bool.
  Context {A} (f : A → bool).

  Lemma list_find_bool_list_find l:
    list_find_bool f l = list_find f l.
  Proof. elim: l => //= ?? ->. case_decide => //=; by case_match. Qed.
End list_find_bool.

Section map_Forall.
  Context `{FinMap K M}.
  Context {A} (P : K → A → Prop).
  Implicit Types m : M A.

  Lemma map_Forall_impl' (Q : K → A → Prop) m :
    map_Forall P m → (∀ i x, m !! i = Some x → P i x → Q i x) → map_Forall Q m.
  Proof. unfold map_Forall; naive_solver. Qed.
  Lemma map_Forall_insert_2' m i x :
    P i x → map_Forall (λ j y, i ≠ j → P j y) m → map_Forall P (<[i:=x]>m).
  Proof using Type*. intros ?? j y; rewrite lookup_insert_Some; naive_solver. Qed.

End map_Forall.

From iris.bi Require Import bi.

Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.
Section sep_map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.
  Lemma big_sepM_kmap {B} `{Countable B} (f : K → B) (Φ : B → A → PROP) m `{!Inj eq eq f}:
    ([∗ map] k↦y ∈ kmap f m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ (f k) y).
  Proof.
    induction m as [|???? IH] using map_ind => /=. { by rewrite kmap_empty !big_sepM_empty. }
    rewrite kmap_insert !big_sepM_insert // ?IH // lookup_kmap_None => ??. by simplify_eq.
  Qed.

  Lemma big_sepM_list_to_map (Φ : K → A → PROP) l:
    NoDup l.*1 →
    ([∗ map] k↦y ∈ list_to_map l, Φ k y) ⊣⊢ ([∗ list] y ∈ l, Φ y.1 y.2).
  Proof.
    induction l as [|?? IH]; csimpl. { by rewrite !big_sepM_empty. }
    move => /NoDup_cons[??]. rewrite big_sepM_insert ?IH //.
    by apply: not_elem_of_list_to_map_1.
  Qed.
End sep_map.
End big_op.


Lemma big_sepL_exist {PROP : bi} {A B} (l : list A) (Φ : _ → _ → _ → PROP) `{!BiAffine PROP} :
  ([∗ list] i↦x∈l, ∃ y : B, Φ i x y) -∗
   ∃ xs : list B, ⌜length xs = length l⌝ ∗ ([∗ list] i↦x∈l, ∃ y : B, ⌜xs !! i = Some y⌝ ∗ Φ i x y).
Proof.
  iIntros "Hl".
  iInduction (l) as [|? l] "IH" forall (Φ).
  { iExists []. iSplit; done. }
  simpl. iDestruct "Hl" as "[[%x Hx] Hl]".
  iDestruct ("IH" with "Hl") as (xs) "[%Heq ?]".
  iExists (x::xs) => /=. iSplit; [by rewrite /= Heq|]. iFrame.
  iExists _. by iFrame.
Qed.

(** fixpoints based on iris/bi/lib/fixpoint.v *)
Class MonoPred {A : Type} (F : (A → Prop) → (A → Prop)) := {
  mono_pred (Φ Ψ : _ → Prop) :
    (∀ x, Φ x → Ψ x) → ∀ x, F Φ x → F Ψ x;
}.
Global Arguments mono_pred {_ _ _} _ _.

Definition least_fixpoint {A : Type}
    (F : (A → Prop) → (A → Prop)) (x : A) : Prop :=
  tc_opaque (∀ Φ : A -> Prop, (∀ x, F Φ x → Φ x) → Φ x).
Global Arguments least_fixpoint : simpl never.
Definition greatest_fixpoint {A : Type}
    (F : (A → Prop) → (A → Prop)) (x : A) : Prop :=
  tc_opaque (∃ Φ : A -> Prop, (∀ x, Φ x → F Φ x) ∧ Φ x).
Global Arguments greatest_fixpoint : simpl never.

Section least.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma least_fixpoint_unfold_2 x : F (least_fixpoint F) x → least_fixpoint F x.
  Proof using Type*.
    rewrite /least_fixpoint /=. move => HF Φ Hincl.
    apply Hincl. apply: mono_pred; [|done].
    move => /= y Hy. apply Hy. done.
  Qed.

  Lemma least_fixpoint_unfold_1 x : least_fixpoint F x → F (least_fixpoint F) x.
  Proof using Type*.
    move => HF. apply HF. move => y Hy /=. apply: mono_pred; [|done].
    move => z Hz. by apply: least_fixpoint_unfold_2.
  Qed.

  Lemma least_fixpoint_unfold x : least_fixpoint F x ↔ F (least_fixpoint F) x.
  Proof using Type*. split; eauto using least_fixpoint_unfold_1, least_fixpoint_unfold_2. Qed.

  Lemma least_fixpoint_ind (Φ : A → Prop) :
    (∀ y, F Φ y → Φ y) → ∀ x, least_fixpoint F x → Φ x.
  Proof. move => HΦ x HF. by apply: HF. Qed.
End least.

Section greatest.
  Context {A : Type} (F : (A → Prop) → (A → Prop)) `{!MonoPred F}.

  Lemma greatest_fixpoint_unfold_1 x :
    greatest_fixpoint F x → F (greatest_fixpoint F) x.
  Proof using Type*.
    move => [Φ [Hincl HΦ]].
    apply: (mono_pred Φ); [| by apply: Hincl].
    move => y Hy. eexists Φ. naive_solver.
  Qed.

  Lemma greatest_fixpoint_unfold_2 x :
    F (greatest_fixpoint F) x → greatest_fixpoint F x.
  Proof using Type*.
    move => HF. eexists (F (greatest_fixpoint F)). split; [|done].
    move => y Hy. apply: mono_pred; [|done]. move => z. apply: greatest_fixpoint_unfold_1.
  Qed.

  Corollary greatest_fixpoint_unfold x :
    greatest_fixpoint F x ↔ F (greatest_fixpoint F) x.
  Proof using Type*.
    split; auto using greatest_fixpoint_unfold_1, greatest_fixpoint_unfold_2.
  Qed.

  Lemma greatest_fixpoint_coind (Φ : A → Prop) :
    (∀ y, Φ y → F Φ y) → ∀ x, Φ x → greatest_fixpoint F x.
  Proof. move => HΦ x Hx. eexists Φ. naive_solver. Qed.
End greatest.
