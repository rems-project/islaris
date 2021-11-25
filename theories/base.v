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
From RecordUpdate Require Export RecordSet.
From iris.proofmode Require Import tactics.
From refinedc.lang Require Export base.
From refinedc.lithium Require Export Z_bitblast.
Require Export isla.bitvector.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Arguments set _ _ _ _ _ !_ /.

Arguments N.mul : simpl never.
Arguments bool_decide : simpl never.
Typeclasses Opaque prefix.

(* TODO: upstream? *)
Typeclasses Opaque Z.ge Z.le.

Ltac unLET :=
  repeat match goal with
         | H := _ |- _ => unfold H in *; clear H
         end.
Tactic Notation "case_match" "as" ident(Hd) :=
  match goal with
  | H : context [ match ?x with _ => _ end ] |- _ => destruct x eqn:Hd
  | |- context [ match ?x with _ => _ end ] => destruct x eqn:Hd
  end.

(* TODO: replace with upsteamed version, https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/337 *)
Lemma ne_Some_eq_None {A} (mx : option A): (∀ x, mx ≠ Some x) → mx = None.
Proof. destruct mx; congruence. Qed.

(* TODO: replace with upsteamed version, https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/337 *)
Lemma Is_true_eq_false (b : bool) : ¬ b ↔ b = false.
Proof. destruct b; naive_solver. Qed.

(* TODO: replace with upsteamed version, https://gitlab.mpi-sws.org/iris/stdpp/-/merge_requests/337 *)
Lemma Z_add_nocarry_lor a b:
  Z.land a b = 0 →
  a + b = Z.lor a b.
Proof. intros ?. rewrite <-Z.lxor_lor by done. by rewrite Z.add_nocarry_lxor. Qed.

(* TODO: replace with upsteamed version *)
Lemma sublist_lookup_Some' {A} i n (l : list A) x:
  sublist_lookup i n l = Some x ↔ x = take n (drop i l) ∧ (i + n <= length l)%nat.
Proof. rewrite /sublist_lookup. case_option_guard; naive_solver lia. Qed.

(* TODO: replace with upsteamed version *)
Lemma reverse_lookup {A} (l : list A) i:
  (i < length l)%nat →
  reverse l !! i = l !! (length l - 1 - i)%nat.
Proof.
  elim: l i => //= x l IH i ?.
  rewrite reverse_cons.
  destruct (decide (i = length l)); subst.
  + rewrite list_lookup_middle ?reverse_length //.
    by have ->: (length l - 0 - length l = 0)%nat by lia.
  + rewrite lookup_app_l ?reverse_length; [|lia].
    rewrite IH; [|lia].
    by have ->: (length l - 0 - i = S (length l - 1 - i))%nat by lia.
Qed.

(* TODO: replace with upsteamed version *)
Lemma reverse_lookup_Some {A} (l : list A) i x:
  reverse l !! i = Some x ↔ l !! (length l - 1 - i)%nat = Some x ∧ (i < length l)%nat.
Proof.
  split.
  - destruct (decide (i < length l)%nat). 1: by rewrite reverse_lookup.
    rewrite lookup_ge_None_2 // reverse_length. lia.
  - move => [??]. by rewrite reverse_lookup.
Qed.

(* TODO: replace with upsteamed version *)
Lemma sum_list_fmap {A} n (l : list A) f:
  (∀ x, x ∈ l → f x = n) →
  sum_list (f <$> l) = (length l * n)%nat.
Proof. move => Hf. elim: l Hf => //; csimpl=> ?? IH Hf. rewrite IH. 2: set_solver. rewrite Hf //. set_solver. Qed.

(* TODO: replace with upsteamed version *)
Lemma sum_list_fmap' {A} (l : list A) n :
  sum_list ((λ _, n) <$> l) = (length l * n)%nat.
Proof. by apply sum_list_fmap. Qed.

(* TODO: replace with upsteamed version *)
Lemma join_lookup_Some {A} (ls : list (list A)) i x:
  mjoin ls !! i = Some x ↔ ∃ j l i', ls !! j = Some l ∧ l !! i' = Some x
                             ∧ i = (sum_list (length <$> take j ls) + i')%nat.
Proof.
  elim: ls i; csimpl. 1: set_solver.
  move => ?? IH i. rewrite lookup_app_Some IH.
  split.
  - case.
    + move => ?. by eexists 0%nat, _, _.
    + move => [? [?[?[?[?[??]]]]]]. eexists (S _), _, _. split_and! => //; csimpl. lia.
  - move => [j [?[?[?[? ->]]]]]. destruct j as [|j]; csimpl in *.
    + left. naive_solver.
    + right. split; [lia|]. eexists _, _, _. split_and! => //. lia.
Qed.

(* TODO: replace with upsteamed version *)
Lemma join_lookup_Some' {A} n (ls : list (list A)) i x:
  (∀ x, x ∈ ls → length x = n) →
  mjoin ls !! i = Some x ↔ ∃ j l i', ls !! j = Some l ∧ l !! i' = Some x
                             ∧ i = (j * n + i')%nat.
Proof.
  move => Hl. rewrite join_lookup_Some. split.
  - move => [?[?[?[Hls [??]]]]]. eexists _, _, _. split_and! => //. subst.
    move: (Hls) => /(lookup_lt_Some _ _ _)?.
    rewrite (sum_list_fmap n) ?take_length_le //; [lia|].
    move => ? /take_elem_of[?[??]]. apply: Hl. by eapply elem_of_list_lookup_2.
  - move => [?[?[?[Hls [??]]]]]. eexists _, _, _. split_and! => //. subst.
    move: (Hls) => /(lookup_lt_Some _ _ _)?.
    rewrite (sum_list_fmap n) ?take_length_le //; [lia|].
    move => ? /take_elem_of[?[??]]. apply: Hl. by eapply elem_of_list_lookup_2.
Qed.

(* TODO: replace with upsteamed version *)
Lemma join_lookup_Some_mul {A} n (ls : list (list A)) j i x:
  (∀ x, x ∈ ls → length x = n) →
  (i < n)%nat →
  mjoin ls !! (j * n + i)%nat = Some x ↔ ∃ l, ls !! j = Some l ∧ l !! i = Some x.
Proof.
  move => Hf ?. rewrite join_lookup_Some' //. split; [| naive_solver].
  move => [j'[l'[i'[?[??]]]]].
  have ? : (i' < n)%nat. { erewrite <-Hf; [| by eapply elem_of_list_lookup_2]. by eapply lookup_lt_Some. }
  have ?: j = j' by nia. subst. have : i = i' by lia. naive_solver.
Qed.

Definition bv_to_bits {n} (b : bv n) : list bool :=
  (λ i, Z.testbit (bv_unsigned b) i) <$> seqZ 0 (Z.of_N n).

Lemma bv_to_bits_length n (b : bv n): length (bv_to_bits b) = N.to_nat n.
Proof. rewrite /bv_to_bits fmap_length seqZ_length. lia. Qed.

Lemma bv_to_bits_lookup_Some n (b : bv n) i x:
  bv_to_bits b !! i = Some x ↔ (i < N.to_nat n)%nat ∧ x = Z.testbit (bv_unsigned b) i.
Proof.
  rewrite /bv_to_bits list_lookup_fmap fmap_Some.
  split.
  - move => [?[/lookup_seqZ? ?]]. naive_solver lia.
  - move => [??]. eexists _. split; [|done]. apply lookup_seqZ. lia.
Qed.

Lemma list_fmap_inj1 {A B} (f1 f2 : A → B) (l : list A) x:
  f1 <$> l = f2 <$> l → x ∈ l → f1 x = f2 x.
Proof. induction l; set_solver. Qed.

Global Instance bv_to_bits_inj n : Inj eq eq (@bv_to_bits n).
Proof.
  unfold bv_to_bits. move => x y /(list_fmap_inj1 _ _ _ _) Hf.
  apply bv_eq_wrap. apply Z.bits_inj_iff' => i Hi.
  rewrite !bv_wrap_spec //. case_bool_decide => //=.
  apply: Hf. apply elem_of_seqZ. lia.
Qed.

Lemma Z_to_little_endian_lookup_Some m n z (i : nat) x:
  0 ≤ m → 0 ≤ n → Z_to_little_endian m n z !! i = Some x ↔ i < m ∧ x = Z.land (z ≫ (i * n)) (Z.ones n).
Proof.
  revert z m. induction i as [|i IH]; intros z m Hm Hn; rewrite -{1}(Z.succ_pred m).
  all: destruct (decide (m = 0)); subst => /=; [ naive_solver lia|].
  all: rewrite Z_to_little_endian_succ /=; [|lia].
  { rewrite Z.shiftr_0_r. naive_solver lia. }
  rewrite IH ?Z.shiftr_shiftr; [|lia..].
  assert ((n + i * n) = (S i * n)) as -> by lia.
  naive_solver lia.
Qed.

Lemma bv_to_little_endian_lookup_Some m n z (i : nat) x:
  0 ≤ m → bv_to_little_endian m n z !! i = Some x ↔ i < m ∧ x = Z_to_bv n (z ≫ (i * Z.of_N n)).
Proof.
  unfold bv_to_little_endian. intros Hm. rewrite list_lookup_fmap fmap_Some.
  split.
  - intros [?[[??]%Z_to_little_endian_lookup_Some ?]]; [|lia..]; subst. split; [done|].
    rewrite -bv_wrap_land. apply bv_eq. by rewrite !Z_to_bv_unsigned bv_wrap_bv_wrap.
  - intros [?->]. eexists _. split; [apply Z_to_little_endian_lookup_Some => //; lia| ].
    rewrite -bv_wrap_land. apply bv_eq. by rewrite !Z_to_bv_unsigned bv_wrap_bv_wrap.
Qed.

Lemma little_endian_to_Z_spec n bs i b:
  0 ≤ i → 0 < n →
  Forall (λ b, 0 ≤ b < 2 ^ n) bs →
  bs !! Z.to_nat (i `div` n) = Some b →
  Z.testbit (little_endian_to_Z n bs) i = Z.testbit b (i `mod` n).
Proof.
  intros Hi Hn. rewrite Z2Nat.inj_div; [|lia..].
  revert i Hi. induction bs as [|b' bs IH]; intros i ? => //= /list.Forall_cons[[? /Z_bounded_iff_bits_nonneg Hb' ]?].
  intros [[?%Nat.div_small_iff ?]|[? Hbs]]%lookup_cons_Some; subst; [|lia|].
  - rewrite Z.lor_spec Z.shiftl_spec // Z.mod_small ?(Z.testbit_neg_r _ (i - n)); [|lia..].
    by rewrite orb_false_r.
  - rewrite Z.lor_spec Z.shiftl_spec //.
    have ? : (Z.to_nat n <= Z.to_nat i)%nat. { apply Nat.div_str_pos_iff; lia. }
    move: Hbs.
    have ->: (Z.to_nat i `div` Z.to_nat n - 1)%nat = (Z.to_nat (i - n) `div` Z.to_nat n)%nat. {
      apply Nat2Z.inj. rewrite Z2Nat.inj_sub ?Nat2Z.inj_div ?Nat2Z.inj_sub ?Nat2Z.inj_div //; [|lia..].
      rewrite -(Z.add_opp_r (Z.to_nat _)) Z.opp_eq_mul_m1 Z.mul_comm Z.div_add; [|lia]. lia.
    }
    move => /IH ->; [|lia|done]. rewrite Hb' /=; [|lia..].
    by rewrite -Zminus_mod_idemp_r Z_mod_same_full Z.sub_0_r.
Qed.

Lemma little_endian_to_bv_spec n bs i b:
  0 ≤ i → n ≠ 0%N →
  bs !! Z.to_nat (i `div` Z.of_N n) = Some b →
  Z.testbit (little_endian_to_bv n bs) i = Z.testbit (bv_unsigned b) (i `mod` Z.of_N n).
Proof.
  move => ???. rewrite /little_endian_to_bv. apply little_endian_to_Z_spec; [lia|lia| |].
  { apply Forall_fmap. apply Forall_true => ? /=. apply bv_unsigned_in_range. }
  rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
Qed.

Lemma bv_seq_length n (x : bv n) len:
  length (bv_seq x len) = Z.to_nat len.
Proof. by rewrite fmap_length seqZ_length. Qed.

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

Lemma Z_of_bool_spec_low b :
  Z.testbit (Z_of_bool b) 0 = b.
Proof. by destruct b. Qed.

Lemma Z_of_bool_spec_high b z:
  0 < z →
  Z.testbit (Z_of_bool b) z = false.
Proof. move => ?. destruct b => /=; by rewrite ?Z.bits_0 // Z_bits_1_above. Qed.

Lemma String_eqb_eq s1 s2:
  (s1 =? s2)%string = bool_decide (s1 = s2).
Proof. case_bool_decide; subst; by rewrite ?String.eqb_eq ?eqb_neq. Qed.

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
