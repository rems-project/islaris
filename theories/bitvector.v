From stdpp Require Export numbers.
From stdpp Require Import countable finite.
From stdpp Require Import options.

Local Open Scope Z_scope.

(* TODO: move *)
Lemma Z_lnot_opp a: Z.lnot a = - a - 1.
Proof. pose proof (Z.add_lnot_diag a). lia. Qed.

(** * Preliminary definitions *)
Definition bv_modulus (n : N) : Z := 2 ^ (Z.of_N n).
Definition bv_half_modulus (n : N) : Z := bv_modulus n `div` 2.
Definition bv_wrap (n : N) (z : Z) : Z := z `mod` bv_modulus n.
Definition bv_swrap (n : N) (z : Z) : Z := bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n.
Local Definition bv_wf (n : N) (z : Z) : Prop := -1 < z < bv_modulus n.

Lemma bv_modulus_pos n :
  0 < bv_modulus n.
Proof. apply Z.pow_pos_nonneg; lia. Qed.
Lemma bv_half_modulus_nonneg n :
  0 ≤ bv_half_modulus n.
Proof. apply Z.div_pos; [|done]. pose proof bv_modulus_pos n. lia. Qed.

Lemma bv_modulus_add n1 n2 :
  bv_modulus (n1 + n2) = bv_modulus n1 * bv_modulus n2.
Proof. unfold bv_modulus. rewrite N2Z.inj_add. eapply Z.pow_add_r; lia. Qed.

Lemma bv_half_modulus_twice n:
  n ≠ 0%N →
  bv_half_modulus n + bv_half_modulus n = bv_modulus n.
Proof.
  intros. unfold bv_half_modulus, bv_modulus.
  rewrite Z.add_diag. symmetry. apply Z_div_exact_2; [lia|].
  rewrite <-Z_pow_pred_r by lia. rewrite Z.mul_comm. by apply Z.mod_mul.
Qed.

Lemma bv_half_modulus_lt_modulus n:
  bv_half_modulus n < bv_modulus n.
Proof.
  pose proof bv_modulus_pos n.
  apply Z_div_lt; [done| lia].
Qed.

Lemma bv_modulus_le_mono n m:
  (n ≤ m)%N →
  bv_modulus n ≤ bv_modulus m.
Proof. intros. apply Z.pow_le_mono; [done|lia]. Qed.
Lemma bv_half_modulus_le_mono n m:
  (n ≤ m)%N →
  bv_half_modulus n ≤ bv_half_modulus m.
Proof. intros. apply Z.div_le_mono; [done|]. by apply bv_modulus_le_mono. Qed.

Lemma bv_modulus_0:
  bv_modulus 0 = 1.
Proof. done. Qed.
Lemma bv_half_modulus_0:
  bv_half_modulus 0 = 0.
Proof. done. Qed.

Lemma bv_half_modulus_twice_mult n:
  bv_half_modulus n + bv_half_modulus n = (if (decide (n = 0%N)) then 0 else 1) * bv_modulus n.
Proof. case_decide; subst; [ rewrite bv_half_modulus_0 | rewrite bv_half_modulus_twice]; lia. Qed.

Lemma bv_wf_in_range n z:
  bv_wf n z ↔ 0 ≤ z < bv_modulus n.
Proof. unfold bv_wf. lia. Qed.

Lemma bv_wrap_in_range n z:
  0 ≤ bv_wrap n z < bv_modulus n.
Proof. apply Z.mod_pos_bound. apply bv_modulus_pos. Qed.

Lemma bv_swrap_in_range n z:
  n ≠ 0%N →
  - bv_half_modulus n ≤ bv_swrap n z < bv_half_modulus n.
Proof.
  intros ?. unfold bv_swrap.
  pose proof bv_half_modulus_twice n.
  pose proof bv_wrap_in_range n (z + bv_half_modulus n).
  lia.
Qed.

Lemma bv_wrap_wf n z :
  bv_wf n (bv_wrap n z).
Proof. pose proof (bv_wrap_in_range n z). split; lia. Qed.

Lemma bv_wrap_small n z :
  0 ≤ z < bv_modulus n → bv_wrap n z = z.
Proof. intros. by apply Z.mod_small. Qed.

Lemma bv_swrap_small n z :
  - bv_half_modulus n ≤ z < bv_half_modulus n →
  bv_swrap n z = z.
Proof.
  intros Hrange. unfold bv_swrap.
  destruct (decide (n = 0%N)); subst.
  { rewrite bv_half_modulus_0 in Hrange. lia. }
  pose proof bv_half_modulus_twice n.
  rewrite bv_wrap_small by lia. lia.
Qed.

Lemma bv_wrap_0 n :
  bv_wrap n 0 = 0.
Proof. done. Qed.
Lemma bv_swrap_0 n :
  bv_swrap n 0 = 0.
Proof.
  pose proof bv_half_modulus_lt_modulus n.
  pose proof bv_half_modulus_nonneg n.
  unfold bv_swrap. rewrite bv_wrap_small; lia.
Qed.

Definition bv_wrap_factor (n : N) (x z : Z) :=
  x = - z `div` bv_modulus n.

Lemma bv_wrap_factor_intro n z :
  ∃ x, bv_wrap_factor n x z ∧ bv_wrap n z = z + x * bv_modulus n.
Proof.
  eexists _. split; [done|].
  pose proof (bv_modulus_pos n). unfold bv_wrap. rewrite Z.mod_eq; lia.
Qed.

Lemma bv_wrap_add_modulus c n z:
  bv_wrap n (z + c * bv_modulus n) = bv_wrap n z.
Proof. apply Z_mod_plus_full. Qed.
Lemma bv_wrap_add_modulus_1 n z:
  bv_wrap n (z + bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus 1 n z). f_equal. lia. Qed.
Lemma bv_wrap_sub_modulus c n z:
  bv_wrap n (z - c * bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus (-c) n z). f_equal. lia. Qed.
Lemma bv_wrap_sub_modulus_1 n z:
  bv_wrap n (z - bv_modulus n) = bv_wrap n z.
Proof. rewrite <-(bv_wrap_add_modulus (-1) n z). done. Qed.

Lemma bv_wrap_add_idemp n x y :
  bv_wrap n (bv_wrap n x + bv_wrap n y) = bv_wrap n (x + y).
Proof. symmetry. apply Zplus_mod. Qed.
Lemma bv_wrap_add_idemp_l n x y :
  bv_wrap n (bv_wrap n x + y) = bv_wrap n (x + y).
Proof. apply Zplus_mod_idemp_l. Qed.
Lemma bv_wrap_add_idemp_r n x y :
  bv_wrap n (x + bv_wrap n y) = bv_wrap n (x + y).
Proof. apply Zplus_mod_idemp_r. Qed.

Lemma bv_wrap_add_inj n x1 x2 y :
  bv_wrap n x1 = bv_wrap n x2 ↔ bv_wrap n (x1 + y) = bv_wrap n (x2 + y).
Proof.
  split; intros Heq.
  - by rewrite <-bv_wrap_add_idemp_l, Heq, bv_wrap_add_idemp_l.
  - pose proof (bv_wrap_factor_intro n (x1 + y)) as [f1[? Hx1]].
    pose proof (bv_wrap_factor_intro n (x2 + y)) as [f2[? Hx2]].
    assert (x1 = x2 + f2 * bv_modulus n - f1 * bv_modulus n) as -> by lia.
    by rewrite bv_wrap_sub_modulus, bv_wrap_add_modulus.
Qed.

Lemma bv_swrap_wrap n z:
  bv_swrap n (bv_wrap n z) = bv_swrap n z.
Proof. unfold bv_swrap, bv_wrap. by rewrite Zplus_mod_idemp_l. Qed.

Lemma bv_wrap_bv_wrap n1 n2 bv :
  (n1 ≤ n2)%N →
  bv_wrap n1 (bv_wrap n2 bv) = bv_wrap n1 bv.
Proof.
  intros ?. unfold bv_wrap.
  rewrite <-Znumtheory.Zmod_div_mod; [done| apply bv_modulus_pos.. |].
  unfold bv_modulus. eexists (2 ^ (Z.of_N n2 - Z.of_N n1)).
  rewrite <-Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma bv_wf_bitwise_op {n} op bop n1 n2 :
  (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
  (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
  bop false false = false →
  bv_wf n n1 → bv_wf n n2 → bv_wf n (op n1 n2).
Proof.
  intros Hbits Hnonneg Hop [? Hok1]%bv_wf_in_range [? Hok2]%bv_wf_in_range. apply bv_wf_in_range.
  split; [lia|].
  apply Z_bounded_iff_bits_nonneg; [lia..|]. intros l ?.
  eapply Z_bounded_iff_bits_nonneg in Hok1;[|try done; lia..].
  eapply Z_bounded_iff_bits_nonneg in Hok2;[|try done; lia..].
  by rewrite Hbits, Hok1, Hok2.
Qed.

Lemma bv_wrap_land n z :
  bv_wrap n z = Z.land z (Z.ones (Z.of_N n)).
Proof. by rewrite Z.land_ones by lia. Qed.

(** * Definition of [bv n] *)
Record bv (n : N) := BV {
  bv_unsigned : Z;
  bv_is_wf : bv_wf n bv_unsigned;
}.
Global Arguments bv_unsigned {_}.
Global Arguments bv_is_wf {_}.
Add Printing Constructor bv.

Global Arguments bv_unsigned : simpl never.

Definition bv_signed {n} (b : bv n) := bv_swrap n (bv_unsigned b).

Lemma bv_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ b1.(bv_unsigned) = b2.(bv_unsigned).
Proof.
  destruct b1, b2. unfold bv_unsigned. split; [ naive_solver|].
  intros. subst. f_equal. apply proof_irrel.
Qed.

Lemma bv_neq n (b1 b2 : bv n) :
  b1 ≠ b2 ↔ b1.(bv_unsigned) ≠ b2.(bv_unsigned).
Proof. unfold not. by rewrite bv_eq. Qed.

Definition Z_to_bv_checked (n : N) (z : Z) : option (bv n) :=
  guard (bv_wf n z) as H; Some (BV n z H).

Program Definition Z_to_bv (n : N) (z : Z) : bv n :=
  BV n (bv_wrap n z) _.
Next Obligation. apply bv_wrap_wf. Qed.

Lemma Z_to_bv_unsigned n z:
  bv_unsigned (Z_to_bv n z) = bv_wrap n z.
Proof. done. Qed.

Lemma Z_to_bv_signed n z:
  bv_signed (Z_to_bv n z) = bv_swrap n z.
Proof. apply bv_swrap_wrap. Qed.

Lemma Z_to_bv_small n z:
  0 ≤ z < bv_modulus n →
  bv_unsigned (Z_to_bv n z) = z.
Proof. rewrite Z_to_bv_unsigned. apply bv_wrap_small. Qed.

Lemma bv_unsigned_in_range n (b : bv n):
  0 ≤ bv_unsigned b < bv_modulus n.
Proof. apply bv_wf_in_range. apply bv_is_wf. Qed.

Lemma bv_eq_wrap n (b1 b2 : bv n) :
  b1 = b2 ↔ bv_wrap n b1.(bv_unsigned) = bv_wrap n b2.(bv_unsigned).
Proof.
  rewrite !bv_wrap_small; [apply bv_eq | apply bv_unsigned_in_range..].
Qed.

Lemma bv_neq_wrap n (b1 b2 : bv n) :
  b1 ≠ b2 ↔ bv_wrap n b1.(bv_unsigned) ≠ bv_wrap n b2.(bv_unsigned).
Proof. unfold not. by rewrite bv_eq_wrap. Qed.

Lemma bv_signed_in_range n (b : bv n):
  n ≠ 0%N →
  - bv_half_modulus n ≤ bv_signed b < bv_half_modulus n.
Proof. apply bv_swrap_in_range. Qed.

Lemma bv_unsigned_spec_high i n (b : bv n) :
  Z.of_N n ≤ i →
  Z.testbit (bv_unsigned b) i = false.
Proof.
  intros ?. pose proof (bv_unsigned_in_range _ b). unfold bv_modulus in *.
  eapply Z_bounded_iff_bits_nonneg; [..|done]; lia.
Qed.

Lemma bv_unsigned_N_0 (b : bv 0):
  bv_unsigned b = 0.
Proof.
  pose proof bv_unsigned_in_range 0 b as H.
  rewrite bv_modulus_0 in H. lia.
Qed.
Lemma bv_signed_N_0 (b : bv 0):
  bv_signed b = 0.
Proof. unfold bv_signed. by rewrite bv_unsigned_N_0, bv_swrap_0. Qed.
Lemma Z_to_bv_checked_bv_unsigned n (b : bv n):
  Z_to_bv_checked n (bv_unsigned b) = Some b.
Proof.
  unfold Z_to_bv_checked. case_option_guard.
  - f_equal. by apply bv_eq.
  - by pose proof bv_is_wf b.
Qed.


Global Program Instance bv_eq_dec n : EqDecision (bv n) := λ '(BV _ v1 p1) '(BV _ v2 p2),
   match decide (v1 = v2) with
   | left eqv => left _
   | right eqv => right _
   end.
Next Obligation.  intros n b1 v1 p1 ? b2 v2 p2 ????. subst. rewrite (proof_irrel p1 p2). exact eq_refl. Defined.
Next Obligation. intros. by injection. Qed.

Global Instance bv_countable n : Countable (bv n) :=
  inj_countable bv_unsigned (Z_to_bv_checked n) (Z_to_bv_checked_bv_unsigned n).

Global Program Instance bv_finite n : Finite (bv n) :=
  {| enum := Z_to_bv n <$> (seqZ 0 (bv_modulus n)) |}.
Next Obligation.
  intros n. apply NoDup_alt. intros i j x.
  rewrite !list_lookup_fmap.
  intros [? [[??]%lookup_seqZ ?]]%fmap_Some.
  intros [? [[??]%lookup_seqZ Hz]]%fmap_Some. subst.
  apply bv_eq in Hz. rewrite !Z_to_bv_small in Hz; lia.
Qed.
Next Obligation.
  intros n x. apply elem_of_list_lookup. eexists (Z.to_nat (bv_unsigned x)).
  rewrite list_lookup_fmap. apply fmap_Some. eexists _.
  pose proof (bv_unsigned_in_range _ x). split.
  - apply lookup_seqZ. split; [done|]. rewrite Z2Nat.id; lia.
  - apply bv_eq. rewrite Z_to_bv_small; rewrite Z2Nat.id; lia.
Qed.


(** * Notation for [bv n] *)
Ltac solve_bitvector_eq :=
  try (vm_compute; exact (conj eq_refl eq_refl));
  lazymatch goal with
    |- bv_wf ?n ?v =>
    fail "Bitvector constant" v "does not fit into" n "bits"
  end.

Notation "'[BV{' l }  v ]" := (BV l v _) (at level 9, only printing) : stdpp_scope.
(* TODO: Somehow the following version creates a warning. *)
(* Notation "'[BV{' l } v ]" := (BV l v _) (at level 9, format "[BV{ l }  v ]", only printing) : stdpp_scope. *)
Notation "'[BV{' l }  v ]" := (BV l v ltac:(solve_bitvector_eq)) (at level 9, only parsing) : stdpp_scope.

(** * Automation *)
Ltac bv_saturate :=
  repeat match goal with b : bv _ |- _ => first [
     learn_hyp (bv_unsigned_in_range _ b) | learn_hyp (bv_signed_in_range _ b)
  ] end.

(* TODO: Where to put the following automation? And how should it best be implemented? *)
Definition bv_wrap_simplify_marker (z1 z2 : Z) : Z := z1 + z2.

Lemma bv_wrap_simplify_marker_intro n z x:
  bv_wrap n (bv_wrap_simplify_marker z 0) = x →
  bv_wrap n z = x.
Proof. intros <-. unfold bv_wrap_simplify_marker. f_equal. lia. Qed.

Lemma bv_wrap_simplify_marker_move n z1 z2 x m:
  bv_wrap n (bv_wrap_simplify_marker z1 (z2 + m)) = x →
  bv_wrap n (bv_wrap_simplify_marker (z1 + z2) m) = x.
Proof. intros <-. unfold bv_wrap_simplify_marker. f_equal. lia. Qed.

Lemma bv_wrap_simplify_marker_remove n z1 z2 x m:
  bv_wrap n (bv_wrap_simplify_marker z1 m) = x →
  bv_wrap n (bv_wrap_simplify_marker (z1 + z2 * bv_modulus n) m) = x.
Proof.
  intros <-. unfold bv_wrap_simplify_marker.
  assert ((z1 + z2 * bv_modulus n + m) = (z1 + m + z2 * bv_modulus n)) as -> by lia.
  by apply bv_wrap_add_modulus.
Qed.

Lemma bv_wrap_simplify_marker_remove_sub n z1 z2 x m:
  bv_wrap n (bv_wrap_simplify_marker z1 m) = x →
  bv_wrap n (bv_wrap_simplify_marker (z1 - z2 * bv_modulus n) m) = x.
Proof.
  intros <-. unfold bv_wrap_simplify_marker.
  assert ((z1 - z2 * bv_modulus n + m) = (z1 + m - z2 * bv_modulus n)) as -> by lia.
  by apply bv_wrap_sub_modulus.
Qed.

Lemma bv_wrap_simplify_marker_move_end n z x m:
  bv_wrap n (z + m) = x →
  bv_wrap n (bv_wrap_simplify_marker z m) = x.
Proof. intros <-. unfold bv_wrap_simplify_marker. f_equal. Qed.

Lemma bv_wrap_simplify_marker_remove_end n z x m:
  bv_wrap n m = x →
  bv_wrap n (bv_wrap_simplify_marker (z * bv_modulus n) m) = x.
Proof. intros <-. unfold bv_wrap_simplify_marker. rewrite Z.add_comm. apply bv_wrap_add_modulus. Qed.

Lemma bv_wrap_simplify_marker_remove_end_opp n z x m:
  bv_wrap n m = x →
  bv_wrap n (bv_wrap_simplify_marker (- z * bv_modulus n) m) = x.
Proof. intros <-. unfold bv_wrap_simplify_marker. rewrite Z.add_comm. apply bv_wrap_add_modulus. Qed.

Lemma Zmul_assoc_comm n2 n1 n3 : n1 * n2 * n3 = n1 * n3 * n2.
Proof. lia. Qed.

Lemma Zpow_2_mul a : a ^ 2 = a * a.
Proof. lia. Qed.

Local Ltac bv_wrap_simplify_cancel :=
  apply bv_wrap_simplify_marker_intro;
  repeat first [ apply bv_wrap_simplify_marker_remove | apply bv_wrap_simplify_marker_remove_sub | apply bv_wrap_simplify_marker_move];
  first [ apply bv_wrap_simplify_marker_remove_end | apply bv_wrap_simplify_marker_remove_end_opp | apply bv_wrap_simplify_marker_move_end].

(** [bv_wrap_simplify] applies for goals of the form [bv_wrap n z1 = bv_wrap n z2] and
[bv_swrap n z1 = bv_swrap n z2] and tries to simplify them by removing any [bv_wrap]
and [bv_swrap] inside z1 and z2. *)
Ltac bv_wrap_simplify :=
  unfold bv_signed, bv_swrap;
  try match goal with | |- _ - _ = _ - _ => f_equal end;
  match goal with
  | |- bv_wrap ?n1 ?z1 = bv_wrap ?n2 ?z2 => change (block bv_wrap n1 z1 = block bv_wrap n2 z2)
  end;
  repeat match goal with
  | |- context [ bv_wrap ?n ?z ] =>
    let x := fresh "x" in
    let Heq := fresh "Heq" in
    pose proof (bv_wrap_factor_intro n z) as [x [? Heq]];
    rewrite !Heq;
    clear Heq
  end;
  match goal with
  | |- block bv_wrap ?n1 ?z1 = block bv_wrap ?n2 ?z2 => change (bv_wrap n1 z1 = bv_wrap n2 z2)
  end;
  match goal with | |- bv_wrap _ ?z = _ => ring_simplify z end;
  match goal with | |- _ = bv_wrap _ ?z => ring_simplify z end;
  repeat rewrite (Z.mul_comm (bv_modulus _));
  repeat rewrite (Z.mul_comm ((bv_modulus _) ^ _));
  repeat rewrite (Zmul_assoc_comm (bv_modulus _));
  repeat rewrite (Zmul_assoc_comm ((bv_modulus _) ^ _));
  repeat rewrite Zpow_2_mul;
  repeat rewrite Z.mul_assoc;

  bv_wrap_simplify_cancel;
  symmetry;
  bv_wrap_simplify_cancel;
  match goal with | |- bv_wrap _ ?z = _ => ring_simplify z end;
  match goal with | |- _ = bv_wrap _ ?z => ring_simplify z end.

Ltac bv_wrap_simplify_solve :=
  bv_wrap_simplify; f_equal; lia.

(** * Operations on [bv n] *)
Program Definition bv_0 (n : N) :=
  BV n 0 _.
Next Obligation.
  intros n. apply bv_wf_in_range. split; [done| apply bv_modulus_pos].
Qed.
Global Instance bv_inhabited n : Inhabited (bv n) := populate (bv_0 n).

Definition bv_succ {n} (x : bv n) : bv n :=
  Z_to_bv n (Z.succ (bv_unsigned x)).
Definition bv_pred {n} (x : bv n) : bv n :=
  Z_to_bv n (Z.pred (bv_unsigned x)).

Definition bv_add {n} (x y : bv n) : bv n := (* SMT: bvadd *)
  Z_to_bv n (Z.add (bv_unsigned x) (bv_unsigned y)).
Definition bv_sub {n} (x y : bv n) : bv n := (* SMT: bvsub *)
  Z_to_bv n (Z.sub (bv_unsigned x) (bv_unsigned y)).
Definition bv_opp {n} (x : bv n) : bv n := (* SMT: bvneg *)
  Z_to_bv n (Z.opp (bv_unsigned x)).

Definition bv_mul {n} (x y : bv n) : bv n := (* SMT: bvmul *)
  Z_to_bv n (Z.mul (bv_unsigned x) (bv_unsigned y)).
Program Definition bv_divu {n} (x y : bv n) : bv n := (* SMT: bvudiv *)
  BV n (Z.div (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_wf_in_range. bv_saturate.
  destruct (decide (bv_unsigned y = 0)) as [->|?].
  { rewrite Zdiv_0_r. lia. }
  split; [ apply Z.div_pos; lia |].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  apply Z.div_le_upper_bound; [ lia|]. nia.
Qed.
Program Definition bv_modu {n} (x y : bv n) : bv n := (* SMT: bvurem *)
  BV n (Z.modulo (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_wf_in_range. bv_saturate.
  destruct (decide (bv_unsigned y = 0)) as [->|?].
  { rewrite Zmod_0_r. lia. }
  split; [ apply Z_mod_pos; lia |].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  apply Z.mod_le; lia.
Qed.
Definition bv_divs {n} (x y : bv n) : bv n :=
  Z_to_bv n (Z.div (bv_signed x) (bv_signed y)).
Definition bv_quots {n} (x y : bv n) : bv n := (* SMT: bvsdiv *)
  Z_to_bv n (Z.quot (bv_signed x) (bv_signed y)).
Definition bv_mods {n} (x y : bv n) : bv n := (* SMT: bvsmod *)
  Z_to_bv n (Z.modulo (bv_signed x) (bv_signed y)).
Definition bv_rems {n} (x y : bv n) : bv n := (* SMT: bvsrem *)
  Z_to_bv n (Z.rem (bv_signed x) (bv_signed y)).

Definition bv_shiftl {n} (x y : bv n) : bv n := (* SMT: bvshl *)
  Z_to_bv n (Z.shiftl (bv_unsigned x) (bv_unsigned y)).
Program Definition bv_shiftr {n} (x y : bv n) : bv n := (* SMT: bvlshr *)
  BV n (Z.shiftr (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_wf_in_range. bv_saturate.
  split; [ apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2; [|lia].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  pose proof (Z.pow_pos_nonneg 2 (bv_unsigned y)).
  apply Z.div_le_upper_bound; [ lia|]. nia.
Qed.
Definition bv_ashiftr {n} (x y : bv n) : bv n := (* SMT: bvashr *)
  Z_to_bv n (Z.shiftr (bv_signed x) (bv_unsigned y)).

Program Definition bv_or {n} (x y : bv n) : bv n := (* SMT: bvor *)
  BV n (Z.lor (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_wf_bitwise_op; [ apply Z.lor_spec | by intros; eapply Z.lor_nonneg | done | apply bv_is_wf..].
Qed.
Program Definition bv_and {n} (x y : bv n) : bv n := (* SMT: bvand *)
  BV n (Z.land (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_wf_bitwise_op; [ apply Z.land_spec | intros; eapply Z.land_nonneg; by left | done | apply bv_is_wf..].
Qed.
Program Definition bv_xor {n} (x y : bv n) : bv n := (* SMT: bvxor *)
  BV n (Z.lxor (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_wf_bitwise_op; [ apply Z.lxor_spec | intros; eapply Z.lxor_nonneg; naive_solver | done | apply bv_is_wf..].
Qed.
Program Definition bv_not {n} (x : bv n) : bv n := (* SMT: bvnot *)
  Z_to_bv n (Z.lnot (bv_unsigned x)).

(* [bv_zero_extends z b] extends [b] to [z] bits with 0. If [z] is
smaller than [n], [b] is truncated. Note that [z] gives the resulting
size instead of the number of bits to add (as SMTLIB does) to avoid a
type-level [_ + _] *)
Program Definition bv_zero_extend {n} (z : N) (b : bv n) : bv z := (* SMT: zero_extend *)
  Z_to_bv z (bv_unsigned b).

Program Definition bv_sign_extend {n} (z : N) (b : bv n) : bv z := (* SMT: sign_extend *)
  Z_to_bv z (bv_signed b).

(* s is start index and l is length. Note that this is different from
extract in SMTLIB which uses [extract (inclusive upper bound)
(inclusive lower bound)]. The version here is phrased in a way that
makes it impossible to use an upper bound that is lower than the lower
bound. *)
Definition bv_extract {n} (s l : N) (b : bv n) : bv l :=
  Z_to_bv l (bv_unsigned b ≫ Z.of_N s).

(* Note that we should always have n1 + n2 = n, but we use a parameter to avoid a type-level (_ + _) *)
Program Definition bv_concat n {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv n := (* SMT: concat *)
  Z_to_bv n (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).

Definition bv_to_little_endian m n (z : Z) : list (bv n) :=
  (λ b, Z_to_bv n b) <$> Z_to_little_endian m (Z.of_N n) z.

Definition little_endian_to_bv n (bs : list (bv n)) : Z :=
  little_endian_to_Z (Z.of_N n) (bv_unsigned <$> bs).

(** * Operations on [bv n] and Z *)
Definition bv_add_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.add (bv_unsigned x) y).
Definition bv_sub_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.sub (bv_unsigned x) y).
Definition bv_mul_Z {n} (x : bv n) (y : Z) : bv n :=
  Z_to_bv n (Z.mul (bv_unsigned x) y).

Definition bv_seq {n} (x : bv n) (len : Z) : list (bv n) :=
  (bv_add_Z x) <$> seqZ 0 len.

(** * Lemmas about [bv n] operations *)

(** ** Unfolding lemmas for the operations. *)
Section unfolding.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_succ_unsigned b :
    bv_unsigned (bv_succ b) = bv_wrap n (Z.succ (bv_unsigned b)).
  Proof. done. Qed.
  Lemma bv_succ_signed b :
    bv_signed (bv_succ b) = bv_swrap n (Z.succ (bv_signed b)).
  Proof. unfold bv_succ. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_pred_unsigned b :
    bv_unsigned (bv_pred b) = bv_wrap n (Z.pred (bv_unsigned b)).
  Proof. done. Qed.
  Lemma bv_pred_signed b :
    bv_signed (bv_pred b) = bv_swrap n (Z.pred (bv_signed b)).
  Proof. unfold bv_pred. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_add_unsigned b1 b2 :
    bv_unsigned (bv_add b1 b2) = bv_wrap n (bv_unsigned b1 + bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_add_signed b1 b2 :
    bv_signed (bv_add b1 b2) = bv_swrap n (bv_signed b1 + bv_signed b2).
  Proof. unfold bv_add. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_sub_unsigned b1 b2 :
    bv_unsigned (bv_sub b1 b2) = bv_wrap n (bv_unsigned b1 - bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_sub_signed b1 b2 :
    bv_signed (bv_sub b1 b2) = bv_swrap n (bv_signed b1 - bv_signed b2).
  Proof. unfold bv_sub. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_opp_unsigned b :
    bv_unsigned (bv_opp b) = bv_wrap n (- bv_unsigned b).
  Proof. done. Qed.
  Lemma bv_opp_signed b :
    bv_signed (bv_opp b) = bv_swrap n (- bv_signed b).
  Proof. unfold bv_opp. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_mul_unsigned b1 b2 :
    bv_unsigned (bv_mul b1 b2) = bv_wrap n (bv_unsigned b1 * bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_mul_signed b1 b2 :
    bv_signed (bv_mul b1 b2) = bv_swrap n (bv_signed b1 * bv_signed b2).
  Proof. unfold bv_mul. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_divu_unsigned b1 b2 :
    bv_unsigned (bv_divu b1 b2) = Z.div (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_divu_signed b1 b2 :
    bv_signed (bv_divu b1 b2) = bv_swrap n (Z.div (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_modu_unsigned b1 b2 :
    bv_unsigned (bv_modu b1 b2) = Z.modulo (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_modu_signed b1 b2 :
    bv_signed (bv_modu b1 b2) = bv_swrap n (Z.modulo (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_divs_unsigned b1 b2 :
    bv_unsigned (bv_divs b1 b2) = bv_wrap n (Z.div (bv_signed b1) (bv_signed b2)).
  Proof. done. Qed.
  Lemma bv_divs_signed b1 b2 :
    bv_signed (bv_divs b1 b2) = bv_swrap n (Z.div (bv_signed b1) (bv_signed b2)).
  Proof. unfold bv_divs. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_quots_unsigned b1 b2 :
    bv_unsigned (bv_quots b1 b2) = bv_wrap n (Z.quot (bv_signed b1) (bv_signed b2)).
  Proof. done. Qed.
  Lemma bv_quots_signed b1 b2 :
    bv_signed (bv_quots b1 b2) = bv_swrap n (Z.quot (bv_signed b1) (bv_signed b2)).
  Proof. unfold bv_quots. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_mods_unsigned b1 b2 :
    bv_unsigned (bv_mods b1 b2) = bv_wrap n (Z.modulo (bv_signed b1) (bv_signed b2)).
  Proof. done. Qed.
  Lemma bv_mods_signed b1 b2 :
    bv_signed (bv_mods b1 b2) = bv_swrap n (Z.modulo (bv_signed b1) (bv_signed b2)).
  Proof. unfold bv_mods. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_rems_unsigned b1 b2 :
    bv_unsigned (bv_rems b1 b2) = bv_wrap n (Z.rem (bv_signed b1) (bv_signed b2)).
  Proof. done. Qed.
  Lemma bv_rems_signed b1 b2 :
    bv_signed (bv_rems b1 b2) = bv_swrap n (Z.rem (bv_signed b1) (bv_signed b2)).
  Proof. unfold bv_rems. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_shiftl_unsigned b1 b2 :
    bv_unsigned (bv_shiftl b1 b2) = bv_wrap n (Z.shiftl (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.
  Lemma bv_shiftl_signed b1 b2 :
    bv_signed (bv_shiftl b1 b2) = bv_swrap n (Z.shiftl (bv_unsigned b1) (bv_unsigned b2)).
  Proof. unfold bv_shiftl. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_shiftr_unsigned b1 b2 :
    bv_unsigned (bv_shiftr b1 b2) = Z.shiftr (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_shiftr_signed b1 b2 :
    bv_signed (bv_shiftr b1 b2) = bv_swrap n (Z.shiftr (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_ashiftr_unsigned b1 b2 :
    bv_unsigned (bv_ashiftr b1 b2) = bv_wrap n (Z.shiftr (bv_signed b1) (bv_unsigned b2)).
  Proof. done. Qed.
  Lemma bv_ashiftr_signed b1 b2 :
    bv_signed (bv_ashiftr b1 b2) = bv_swrap n (Z.shiftr (bv_signed b1) (bv_unsigned b2)).
  Proof. unfold bv_ashiftr. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_or_unsigned b1 b2 :
    bv_unsigned (bv_or b1 b2) = Z.lor (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_or_signed b1 b2 :
    bv_signed (bv_or b1 b2) = bv_swrap n (Z.lor (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_and_unsigned b1 b2 :
    bv_unsigned (bv_and b1 b2) = Z.land (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_and_signed b1 b2 :
    bv_signed (bv_and b1 b2) = bv_swrap n (Z.land (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_xor_unsigned b1 b2 :
    bv_unsigned (bv_xor b1 b2) = Z.lxor (bv_unsigned b1) (bv_unsigned b2).
  Proof. done. Qed.
  Lemma bv_xor_signed b1 b2 :
    bv_signed (bv_xor b1 b2) = bv_swrap n (Z.lxor (bv_unsigned b1) (bv_unsigned b2)).
  Proof. done. Qed.

  Lemma bv_not_unsigned b :
    bv_unsigned (bv_not b) = bv_wrap n (Z.lnot (bv_unsigned b)).
  Proof. done. Qed.
  Lemma bv_not_signed b :
    bv_signed (bv_not b) = bv_swrap n (Z.lnot (bv_unsigned b)).
  Proof. unfold bv_not. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_zero_extend_unsigned' z b :
    bv_unsigned (bv_zero_extend z b) = bv_wrap z (bv_unsigned b).
  Proof. done. Qed.
  (* [bv_zero_extend_unsigned] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_zero_extend_unsigned z b :
    (n ≤ z)%N →
    bv_unsigned (bv_zero_extend z b) = bv_unsigned b.
  Proof.
    intros ?. rewrite bv_zero_extend_unsigned', bv_wrap_small; [done|].
    bv_saturate. pose proof (bv_modulus_le_mono n z). lia.
  Qed.
  Lemma bv_zero_extend_signed z b :
    bv_signed (bv_zero_extend z b) = bv_swrap z (bv_unsigned b).
  Proof. unfold bv_zero_extend. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_sign_extend_unsigned z b :
    bv_unsigned (bv_sign_extend z b) = bv_wrap z (bv_signed b).
  Proof. done. Qed.
  Lemma bv_sign_extend_signed' z b :
    bv_signed (bv_sign_extend z b) = bv_swrap z (bv_signed b).
  Proof. unfold bv_sign_extend. rewrite Z_to_bv_signed. done. Qed.
  (* [bv_sign_extend_signed] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_sign_extend_signed z b :
    (n ≤ z)%N →
    bv_signed (bv_sign_extend z b) = bv_signed b.
  Proof.
    intros ?. rewrite bv_sign_extend_signed'.
    destruct (decide (n = 0%N)); subst.
    { by rewrite bv_signed_N_0, bv_swrap_0. }
    apply bv_swrap_small. bv_saturate.
    pose proof bv_half_modulus_le_mono n z. lia.
  Qed.

  Lemma bv_extract_unsigned s l b :
    bv_unsigned (bv_extract s l b) = bv_wrap l (bv_unsigned b ≫ Z.of_N s).
  Proof. done. Qed.
  Lemma bv_extract_signed s l b :
    bv_signed (bv_extract s l b) = bv_swrap l (bv_unsigned b ≫ Z.of_N s).
  Proof. unfold bv_extract. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_concat_unsigned' m  n2 b1 (b2 : bv n2) :
    bv_unsigned (bv_concat m b1 b2) = bv_wrap m (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).
  Proof. done. Qed.
  (* [bv_concat_unsigned'] is the version that we want, but it
  only holds with a precondition. *)
  Lemma bv_concat_unsigned m n2 b1 (b2 : bv n2) :
    (m = n + n2)%N →
    bv_unsigned (bv_concat m b1 b2) = Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2).
  Proof.
    intros ->. rewrite bv_concat_unsigned', bv_wrap_small; [done|].
    apply Z_bounded_iff_bits_nonneg'; [lia | |].
    { apply Z.lor_nonneg. bv_saturate. split; [|lia]. apply Z.shiftl_nonneg. lia. }
    intros k ?. rewrite Z.lor_spec, Z.shiftl_spec; [|lia].
    apply orb_false_intro; (eapply Z_bounded_iff_bits_nonneg; [..|done]); bv_saturate; try lia.
    - apply (Z.lt_le_trans _ (bv_modulus n)); [lia|]. apply Z.pow_le_mono_r; lia.
    - apply (Z.lt_le_trans _ (bv_modulus n2)); [lia|]. apply Z.pow_le_mono_r; lia.
  Qed.
  Lemma bv_concat_signed m n2 b1 (b2 : bv n2) :
    bv_signed (bv_concat m b1 b2) = bv_swrap m (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).
  Proof. unfold bv_concat. rewrite Z_to_bv_signed. done. Qed.

  Lemma bv_add_Z_unsigned b z :
    bv_unsigned (bv_add_Z b z) = bv_wrap n (bv_unsigned b + z).
  Proof. done. Qed.
  Lemma bv_add_Z_signed b z :
    bv_signed (bv_add_Z b z) = bv_swrap n (bv_signed b + z).
  Proof. unfold bv_add_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_sub_Z_unsigned b z :
    bv_unsigned (bv_sub_Z b z) = bv_wrap n (bv_unsigned b - z).
  Proof. done. Qed.
  Lemma bv_sub_Z_signed b z :
    bv_signed (bv_sub_Z b z) = bv_swrap n (bv_signed b - z).
  Proof. unfold bv_sub_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.

  Lemma bv_mul_Z_unsigned b z:
    bv_unsigned (bv_mul_Z b z) = bv_wrap n (bv_unsigned b * z).
  Proof. done. Qed.
  Lemma bv_mul_Z_signed b z :
    bv_signed (bv_mul_Z b z) = bv_swrap n (bv_signed b * z).
  Proof. unfold bv_mul_Z. rewrite Z_to_bv_signed. bv_wrap_simplify_solve. Qed.
End unfolding.

(** ** Properties of bv operations *)
Section properties.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_sub_add_opp b1 b2:
    bv_sub b1 b2 = bv_add b1 (bv_opp b2).
  Proof.
    apply bv_eq. unfold bv_sub, bv_add, bv_opp. rewrite !Z_to_bv_unsigned.
    bv_wrap_simplify_solve.
  Qed.

  Global Instance bv_add_assoc : Assoc (=) (@bv_add n).
  Proof.
    intros ???. unfold bv_add. apply bv_eq. rewrite !Z_to_bv_unsigned.
    bv_wrap_simplify_solve.
  Qed.

  Global Instance bv_mul_assoc : Assoc (=) (@bv_mul n).
  Proof.
    intros ???. unfold bv_mul. apply bv_eq. rewrite !Z_to_bv_unsigned.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_0 b : bv_add_Z b 0 = b.
  Proof.
    unfold bv_add_Z. rewrite Z.add_0_r.
    apply bv_eq. apply Z_to_bv_small. apply bv_unsigned_in_range.
  Qed.

  Lemma bv_add_Z_add_r b m o:
    bv_add_Z b (m + o) = bv_add_Z (bv_add_Z b o) m.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
     bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_add_l b m o:
    bv_add_Z b (m + o) = bv_add_Z (bv_add_Z b m) o.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
     bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_Z_succ b m:
    bv_add_Z b (Z.succ m) = bv_add_Z (bv_add_Z b 1) m.
  Proof.
    apply bv_eq. unfold bv_add_Z. rewrite !Z_to_bv_unsigned.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_not_opp b:
    bv_not b = bv_sub_Z (bv_opp b) 1.
  Proof.
    apply bv_eq.
    rewrite bv_not_unsigned, bv_sub_Z_unsigned, bv_opp_unsigned, Z_lnot_opp.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_concat_0 m n2 b1 (b2 : bv n2) :
    bv_unsigned b1 = 0 →
    bv_concat m b1 b2 = bv_zero_extend m b2.
  Proof.
    intros Hb1. apply bv_eq.
    by rewrite bv_zero_extend_unsigned', bv_concat_unsigned', Hb1, Z.shiftl_0_l, Z.lor_0_l.
  Qed.
End properties.

(** ** Lemmas about [bv_to_little] and [bv_of_little] *)
Section little.

  Lemma bv_to_litte_endian_unsigned m n z:
    0 ≤ m →
    bv_unsigned <$> bv_to_little_endian m n z = Z_to_little_endian m (Z.of_N n) z.
  Proof.
    intros ?. apply list_eq. intros i. unfold bv_to_little_endian.
    rewrite list_lookup_fmap, list_lookup_fmap.
    destruct (Z_to_little_endian m (Z.of_N n) z !! i) eqn: Heq; [simpl |done].
    rewrite Z_to_bv_small; [done|].
    eapply (Forall_forall (λ z, _ ≤ z < _)); [ |by eapply elem_of_list_lookup_2].
    eapply Z_to_little_endian_bound; lia.
  Qed.

  Lemma bv_to_little_endian_to_bv m n bs:
    m = Z.of_nat (length bs) →
    bv_to_little_endian m n (little_endian_to_bv n bs) = bs.
  Proof.
    intros ->. eapply (fmap_inj bv_unsigned). { intros ???. by apply bv_eq. }
    rewrite bv_to_litte_endian_unsigned; [|lia].
    apply Z_to_little_endian_to_Z; [by rewrite fmap_length | lia |].
    apply Forall_forall. intros ? [?[->?]]%elem_of_list_fmap_2. apply bv_unsigned_in_range.
  Qed.

  Lemma little_endian_to_bv_to_little_endian m n z:
    0 ≤ m →
    little_endian_to_bv n (bv_to_little_endian m n z) = z `mod` 2 ^ (m * Z.of_N n).
  Proof.
    intros ?. unfold little_endian_to_bv.
    rewrite bv_to_litte_endian_unsigned; [|lia].
    apply little_endian_to_Z_to_little_endian; lia.
  Qed.

  Lemma bv_to_little_endian_length m n z :
    0 ≤ m →
    length (bv_to_little_endian m n z) = Z.to_nat m.
  Proof.
    intros ?. unfold bv_to_little_endian. rewrite fmap_length.
    apply Nat2Z.inj. rewrite Z_to_little_endian_length, ?Z2Nat.id; try lia.
  Qed.

  Lemma bv_of_to_little_bv x m n (b : bv x):
    0 ≤ m →
    x = (Z.to_N m * n)%N →
    Z_to_bv x (little_endian_to_bv n (bv_to_little_endian m n (bv_unsigned b))) = b.
  Proof.
    intros ? ->. rewrite little_endian_to_bv_to_little_endian, Z.mod_small; [| |lia].
    - apply bv_eq. rewrite Z_to_bv_small; [done|]. apply bv_unsigned_in_range.
    - pose proof bv_unsigned_in_range _ b as Hr. unfold bv_modulus in Hr.
      by rewrite N2Z.inj_mul, Z2N.id in Hr.
  Qed.
End little.

(** ** Lemmas about [bv_seq] *)
Section bv_seq.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_seq_succ b m:
    0 ≤ m →
    bv_seq b (Z.succ m) = b :: bv_seq (bv_add_Z b 1) m.
  Proof.
    intros. unfold bv_seq. rewrite seqZ_cons by lia. csimpl.
    rewrite bv_add_Z_0. f_equal.
    assert (Z.succ 0 = 1 + 0) as -> by lia.
    rewrite <-fmap_add_seqZ, <-list_fmap_compose. apply list_fmap_ext.
    - intros x. simpl. by rewrite bv_add_Z_add_l.
    - f_equal. lia.
  Qed.
End bv_seq.

(** * [bvn] *)
Record bvn := BVN {
  bvn_n : N;
  bvn_val : bv bvn_n;
}.

Definition bvn_unsigned (b : bvn) := bv_unsigned (b.(bvn_val)).

Lemma bvn_eq (b1 b2 : bvn) :
  b1 = b2 ↔ b1.(bvn_n) = b2.(bvn_n) ∧ bvn_unsigned b1 = bvn_unsigned b2.
Proof. split; [ naive_solver|]. destruct b1, b2; simpl; intros [??]. subst. f_equal. by apply bv_eq. Qed.

Global Program Instance bvn_eq_dec : EqDecision bvn := λ '(BVN n1 b1) '(BVN n2 b2),
   match decide (n1 = n2) with
   | left eqv => match decide (bv_unsigned b1 = bv_unsigned b2) with
                | left eqb => left _
                | right eqb => right _
                end
   | right eqv => right _
   end.
(* TODO: The following does not compute to eq_refl*)
Next Obligation. intros. apply bvn_eq. naive_solver. Qed.
Next Obligation. intros. intros ?%bvn_eq. naive_solver. Qed.
Next Obligation. intros. intros ?%bvn_eq. naive_solver. Qed.

Definition bvn_to_bv (n : N) (b : bvn) : option (bv n) :=
  match decide (b.(bvn_n) = n) with
  | left eq => Some (eq_rect (bvn_n b) (λ n0 : N, bv n0) (bvn_val b) n eq)
  | right _ => None
  end.
Global Arguments bvn_to_bv !_ !_ /.

Definition bv_to_bvn {n} (b : bv n) : bvn := BVN _ b.
Coercion bv_to_bvn : bv >-> bvn.

(** * tests *)
Section test.
Goal ([BV{10} 3 ] = [BV{10} 5]). Abort.
Fail Goal ([BV{2} 3 ] = [BV{10} 5]).
Goal ([BV{2} 3 ] =@{bvn} [BV{10} 5]). Abort.
Fail Goal ([BV{2} 4 ] = [BV{2} 5]).
Goal bvn_to_bv 2 [BV{2} 3] = Some [BV{2} 3]. done. Abort.
End test.
