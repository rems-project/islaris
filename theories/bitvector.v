From stdpp Require Export numbers.
From stdpp Require Import countable finite.
From stdpp Require Import options.

Local Open Scope Z_scope.

Lemma Z_bounded_iff_bits_nonneg k n :
  0 ≤ k → 0 ≤ n →
  n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false.
Proof.
  intros.
  destruct (decide (n = 0)) as [->|].
  - setoid_rewrite Z.bits_0. split; [done|]. intros. by apply Z.pow_pos_nonneg.
  - split.
    + intros Hb%Z.log2_lt_pow2 l Hl; [| lia]. apply Z.bits_above_log2; lia.
    + intros Hl.
      destruct (decide (n < 2^k)); [done|].
      assert (Z.testbit n (Z.log2 n) = false) as Hbit.
      { apply Hl, Z.log2_le_pow2; lia. }
      rewrite Z.bit_log2 in Hbit; [done| lia].
Qed.

Lemma Z_bounded_iff_bits_nonneg' k n :
  0 ≤ k → 0 ≤ n →
  0 ≤ n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false.
Proof.
  intros ??. split.
  - intros ?. apply Z_bounded_iff_bits_nonneg; lia.
  - intros ?%Z_bounded_iff_bits_nonneg; lia.
Qed.

Tactic Notation "learn_hyp" constr(p) "as" ident(H') :=
  let P := type of p in
  match goal with
  | H : P |- _ => fail 1
  | _ => pose proof p as H'
  end.
Tactic Notation "learn_hyp" constr(p) :=
  let H := fresh in learn_hyp p as H.

Lemma Zmul_assoc_comm n2 n1 n3 : n1 * n2 * n3 = n1 * n3 * n2.
Proof. lia. Qed.

Lemma Zpow_2_mul a : a ^ 2 = a * a.
Proof. lia. Qed.

Fixpoint Z_to_little (m : nat) (n : Z) (z : Z) : list Z :=
  match m with
  | O => []
  | S m' => Z.land z (Z.ones n) :: Z_to_little m' n (z ≫ n)
  end.

Fixpoint Z_of_little (n : Z) (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => Z.lor (Z_of_little n bs' ≪ n) b
  end.

Lemma Z_to_little_len (m : nat) (n z : Z) : length (Z_to_little m n z) = m.
Proof.
  revert z.
  induction m; cbn; [done|].
  intro z. rewrite IHm. reflexivity.
Qed.

Lemma Z_ones_spec n m:
  0 ≤ m → 0 ≤ n →
  Z.testbit (Z.ones n) m = if decide (m < n) then true else false.
Proof. intros. case_decide; [ by rewrite Z.ones_spec_low by lia | by rewrite Z.ones_spec_high by lia ]. Qed.

Lemma Z_to_of_little m n bs:
  m = length bs → 0 ≤ n →
  Forall (λ b, 0 ≤ b < 2 ^ n) bs →
  Z_to_little m n (Z_of_little n bs) = bs.
Proof.
  intros -> ? Hall. induction Hall as [|b bs ? ? IH]; [done|]; csimpl.
  f_equal.
  - apply Z.bits_inj_iff'. intros n' ?.
    rewrite !Z.land_spec, Z.lor_spec, Z_ones_spec by lia.
    case_decide.
    + rewrite andb_true_r, Z.shiftl_spec_low by lia. done.
    + rewrite !andb_false_r by lia.
      symmetry. eapply (Z_bounded_iff_bits_nonneg n); lia.
  - rewrite <-IH at 3. f_equal.
    apply Z.bits_inj_iff'. intros n' ?.
    rewrite Z.shiftr_spec, Z.lor_spec, Z.shiftl_spec by lia.
    assert (Z.testbit b (n' + n) = false) as ->. {
      eapply (Z_bounded_iff_bits_nonneg n); lia.
    }
    rewrite orb_false_r. f_equal. lia.
Qed.

Lemma Z_of_to_little m n z:
  0 ≤ n →
  Z_of_little n (Z_to_little m n z) = z `mod` 2 ^ (m * n).
Proof.
  intros. rewrite <-Z.land_ones by nia.
  revert z. induction m as [|m IH]; simpl. { intros. Z.bitwise. by rewrite andb_false_r. }
  intros z. rewrite IH.
  apply Z.bits_inj_iff'. intros n' ?.
  rewrite Z.land_spec, Z.lor_spec, Z.shiftl_spec, !Z.land_spec by lia.
  rewrite (Z_ones_spec n n') by lia. case_decide.
  - rewrite andb_true_r. rewrite Z.testbit_neg_r by lia. simpl.
    rewrite Z_ones_spec by nia. case_decide; [ by rewrite andb_true_r| nia].
  - rewrite andb_false_r, orb_false_r.
    rewrite Z.shiftr_spec by lia. f_equal. { f_equal. lia. }
    rewrite !Z_ones_spec by nia. repeat case_decide; try done; nia.
Qed.

Lemma Z_to_little_bound x m n z:
  0 ≤ n →
  x ∈ Z_to_little m n z → 0 ≤ x < 2 ^ n.
Proof.
  intros ?. revert z. induction m as [|m IH]; simpl. { by intros ? ?%elem_of_nil. }
  intros ?. intros [->|?%IH]%elem_of_cons; [|done].
  rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma Z_of_little_bound n bs:
  0 ≤ n →
  Forall (λ b, 0 ≤ b < 2 ^ n) bs →
  0 ≤ Z_of_little n bs < 2 ^ ((length bs) * n).
Proof.
  intros ? Hall.
  induction Hall as [|b bs Hb ? IH]; [done|]; simpl.
  apply Z_bounded_iff_bits_nonneg'; [ nia | |].
  - apply Z.lor_nonneg. split; [|lia]. apply Z.shiftl_nonneg. lia.
  - intros l ?. rewrite Z.lor_spec.
    eapply Z_bounded_iff_bits_nonneg' in Hb.
    + erewrite Hb, orb_false_r.
      rewrite Z.shiftl_spec by nia.
      eapply Z_bounded_iff_bits_nonneg'; [| | done |]; nia.
    + lia.
    + lia.
    + nia.
Qed.


(** * Preliminary definitions *)
Definition bv_modulus (n : N) : Z := 2 ^ (Z.of_N n).
Definition bv_half_modulus (n : N) : Z := bv_modulus n `div` 2.
Definition bv_wrap (n : N) (z : Z) : Z := z `mod` bv_modulus n.
Definition bv_swrap (n : N) (z : Z) : Z := bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n.
Definition bv_ok (n : N) (z : Z) : Prop := -1 < z < bv_modulus n.

Lemma bv_modulus_pos n :
  0 < bv_modulus n.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

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

Lemma bv_half_modulus_0:
  bv_half_modulus 0 = 0.
Proof. done. Qed.

Lemma bv_half_modulus_twice_mult n:
  bv_half_modulus n + bv_half_modulus n = (if (decide (n = 0%N)) then 0 else 1) * bv_modulus n.
Proof. case_decide; subst; [ rewrite bv_half_modulus_0 | rewrite bv_half_modulus_twice]; lia. Qed.

Lemma bv_ok_in_range n z:
  bv_ok n z ↔ 0 ≤ z < bv_modulus n.
Proof. unfold bv_ok. lia. Qed.

Lemma bv_wrap_ok n z :
  bv_ok n (bv_wrap n z).
Proof.
  unfold bv_wrap.
  pose proof (Z.mod_pos_bound z (bv_modulus n)) as [??]. { apply bv_modulus_pos. }
  split; lia.
Qed.

Lemma bv_wrap_small n z :
  0 ≤ z < bv_modulus n → bv_wrap n z = z.
Proof. intros. by apply Z.mod_small. Qed.

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

Lemma bv_ok_bitwise_op {n} op bop n1 n2 :
  (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
  (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
  bop false false = false →
  bv_ok n n1 → bv_ok n n2 → bv_ok n (op n1 n2).
Proof.
  intros Hbits Hnonneg Hop [? Hok1]%bv_ok_in_range [? Hok2]%bv_ok_in_range. apply bv_ok_in_range.
  split; [lia|].
  apply Z_bounded_iff_bits_nonneg; [lia..|]. intros l ?.
  eapply Z_bounded_iff_bits_nonneg in Hok1;[|try done; lia..].
  eapply Z_bounded_iff_bits_nonneg in Hok2;[|try done; lia..].
  by rewrite Hbits, Hok1, Hok2.
Qed.

(** * Definition of [bv n] *)
Record bv (n : N) := BV {
  bv_unsigned : Z;
  bv_is_ok : bv_ok n bv_unsigned;
}.
Global Arguments bv_unsigned {_}.
Global Arguments bv_is_ok {_}.

Definition bv_signed {n} (b : bv n) := bv_swrap n (bv_unsigned b).

Lemma bv_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ b1.(bv_unsigned) = b2.(bv_unsigned).
Proof.
  destruct b1, b2. split; simpl; [ naive_solver|].
  intros. subst. f_equal. apply proof_irrel.
Qed.

Global Program Instance bv_eq_dec n : EqDecision (bv n) := λ '(BV _ v1 p1) '(BV _ v2 p2),
   match decide (v1 = v2) with
   | left eqv => left _
   | right eqv => right _
   end.
Next Obligation. intros. subst. rewrite (proof_irrel p1 p2). exact eq_refl. Defined.
Next Obligation. intros. by injection. Qed.

Global Instance bv_countable n : Countable (bv n).
Proof.
  refine (inj_countable bv_unsigned
    (λ x, match decide (bv_ok n x) with | left b => Some (BV n x b) | _ => None end) _).
  intros x. case_decide; [ f_equal; by apply bv_eq|].
  by pose proof bv_is_ok x.
Qed.

Definition bv_of_Z_checked (n : N) (z : Z) : option (bv n) :=
  match decide (bv_ok n z) with
  | left Heq => Some (BV n z Heq)
  | right _ => None
  end.

Program Definition bv_of_Z (n : N) (z : Z) : bv n :=
  BV n (bv_wrap n z) _.
Next Obligation. apply bv_wrap_ok. Qed.

Lemma bv_of_Z_unsigned n z:
  bv_unsigned (bv_of_Z n z) = bv_wrap n z.
Proof. done. Qed.

Lemma bv_unsigned_bv_of_Z n b:
  bv_of_Z n (bv_unsigned b) = b.
Proof.
  destruct b.
  apply bv_eq.
  cbn.
  apply bv_wrap_small.
  by apply bv_ok_in_range.
Qed.

Lemma bv_of_Z_signed n z:
  bv_signed (bv_of_Z n z) = bv_swrap n z.
Proof. apply bv_swrap_wrap. Qed.

Global Arguments bv_of_Z : simpl never.
Global Opaque bv_of_Z.

Lemma bv_of_Z_small n z:
  0 ≤ z < bv_modulus n →
  bv_unsigned (bv_of_Z n z) = z.
Proof. rewrite bv_of_Z_unsigned. apply bv_wrap_small. Qed.

Lemma bv_in_range n (b : bv n):
  0 ≤ bv_unsigned b < bv_modulus n.
Proof. apply bv_ok_in_range. apply bv_is_ok. Qed.

Global Program Instance bv_finite n : Finite (bv n) :=
  {| enum := bv_of_Z n <$> (seqZ 0 (bv_modulus n)) |}.
Next Obligation.
  intros n. apply NoDup_alt. intros i j x.
  rewrite !list_lookup_fmap.
  intros [? [[??]%lookup_seqZ ?]]%fmap_Some.
  intros [? [[??]%lookup_seqZ Hz]]%fmap_Some. subst.
  apply bv_eq in Hz. rewrite !bv_of_Z_small in Hz; lia.
Qed.
Next Obligation.
  intros. apply elem_of_list_lookup. eexists (Z.to_nat (bv_unsigned x)).
  rewrite list_lookup_fmap. apply fmap_Some. eexists _.
  pose proof (bv_in_range _ x). split.
  - apply lookup_seqZ. split; [done|]. rewrite Z2Nat.id; lia.
  - apply bv_eq. rewrite bv_of_Z_small; rewrite Z2Nat.id; lia.
Qed.


(** * Notation for [bv n] *)
Ltac solve_bitvector_eq :=
  try (vm_compute; done);
  lazymatch goal with
  | |- -1 < ?v < 2 ^ ?l =>
    fail "Bitvector constant" v "does not fit into" l "bits"
  end.

Notation "'[BV{' l }  v ]" := (BV l v _) (at level 9, only printing) : stdpp_scope.
(* TODO: Somehow the following version creates a warning. *)
(* Notation "'[BV{' l } v ]" := (BV l v _) (at level 9, format "[BV{ l }  v ]", only printing) : stdpp_scope. *)
(* TODO: This notation breaks when used in gmap notations. Why? *)
Notation "'[BV{' l }  v ]" := (BV l v ltac:(solve_bitvector_eq)) (at level 9, only parsing) : stdpp_scope.

(** * Automation *)
Ltac bv_saturate :=
  repeat match goal with | b : bv _ |- _ => learn_hyp (bv_in_range _ b) end.

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

Ltac bv_wrap_simplify_cancel :=
  apply bv_wrap_simplify_marker_intro;
  repeat first [ apply bv_wrap_simplify_marker_remove | apply bv_wrap_simplify_marker_remove_sub | apply bv_wrap_simplify_marker_move];
  first [ apply bv_wrap_simplify_marker_remove_end | apply bv_wrap_simplify_marker_remove_end_opp | apply bv_wrap_simplify_marker_move_end].

Ltac bv_wrap_simplify :=
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
  intros n. apply bv_ok_in_range. split; [done| apply bv_modulus_pos].
Qed.

Definition bv_succ {n} (x : bv n) : bv n :=
  bv_of_Z n (Z.succ (bv_unsigned x)).
Definition bv_pred {n} (x : bv n) : bv n :=
  bv_of_Z n (Z.pred (bv_unsigned x)).

Definition bv_add {n} (x y : bv n) : bv n := (* SMT: bvadd *)
  bv_of_Z n (Z.add (bv_unsigned x) (bv_unsigned y)).
Definition bv_sub {n} (x y : bv n) : bv n := (* SMT: bvsub *)
  bv_of_Z n (Z.sub (bv_unsigned x) (bv_unsigned y)).
Definition bv_opp {n} (x : bv n) : bv n := (* SMT: bvneg *)
  bv_of_Z n (Z.opp (bv_unsigned x)).

Definition bv_mul {n} (x y : bv n) : bv n := (* SMT: bvmul *)
  bv_of_Z n (Z.mul (bv_unsigned x) (bv_unsigned y)).
Program Definition bv_divu {n} (x y : bv n) : bv n := (* SMT: bvudiv *)
  BV n (Z.div (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_ok_in_range. bv_saturate.
  destruct (decide (bv_unsigned y = 0)) as [->|?].
  { rewrite Zdiv_0_r. lia. }
  split; [ apply Z.div_pos; lia |].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  apply Z.div_le_upper_bound; [ lia|]. nia.
Qed.
Program Definition bv_modu {n} (x y : bv n) : bv n := (* SMT: bvurem *)
  BV n (Z.modulo (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_ok_in_range. bv_saturate.
  destruct (decide (bv_unsigned y = 0)) as [->|?].
  { rewrite Zmod_0_r. lia. }
  split; [ apply Z_mod_pos; lia |].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  apply Z.mod_le; lia.
Qed.
Definition bv_divs {n} (x y : bv n) : bv n :=
  bv_of_Z n (Z.div (bv_signed x) (bv_signed y)).
Definition bv_quots {n} (x y : bv n) : bv n := (* SMT: bvsdiv *)
  bv_of_Z n (Z.quot (bv_signed x) (bv_signed y)).
Definition bv_mods {n} (x y : bv n) : bv n := (* SMT: bvsmod *)
  bv_of_Z n (Z.modulo (bv_signed x) (bv_signed y)).
Definition bv_rems {n} (x y : bv n) : bv n := (* SMT: bvsrem *)
  bv_of_Z n (Z.rem (bv_signed x) (bv_signed y)).

Definition bv_shiftl {n} (x y : bv n) : bv n := (* SMT: bvshl *)
  bv_of_Z n (Z.shiftl (bv_unsigned x) (bv_unsigned y)).
Program Definition bv_shiftr {n} (x y : bv n) : bv n := (* SMT: bvlshr *)
  BV n (Z.shiftr (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros n x y. apply bv_ok_in_range. bv_saturate.
  split; [ apply Z.shiftr_nonneg; lia|].
  rewrite Z.shiftr_div_pow2; [|lia].
  apply (Z.le_lt_trans _ (bv_unsigned x)); [|lia].
  pose proof (Z.pow_pos_nonneg 2 (bv_unsigned y)).
  apply Z.div_le_upper_bound; [ lia|]. nia.
Qed.
Definition bv_ashiftr {n} (x y : bv n) : bv n := (* SMT: bvashr *)
  bv_of_Z n (Z.shiftr (bv_signed x) (bv_unsigned y)).

Program Definition bv_or {n} (x y : bv n) : bv n := (* SMT: bvor *)
  BV n (Z.lor (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_ok_bitwise_op; [ apply Z.lor_spec | by intros; eapply Z.lor_nonneg | done | apply bv_is_ok..].
Qed.
Program Definition bv_and {n} (x y : bv n) : bv n := (* SMT: bvand *)
  BV n (Z.land (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_ok_bitwise_op; [ apply Z.land_spec | intros; eapply Z.land_nonneg; by left | done | apply bv_is_ok..].
Qed.
Program Definition bv_xor {n} (x y : bv n) : bv n := (* SMT: bvxor *)
  BV n (Z.lxor (bv_unsigned x) (bv_unsigned y)) _.
Next Obligation.
  intros. eapply bv_ok_bitwise_op; [ apply Z.lxor_spec | intros; eapply Z.lxor_nonneg; naive_solver | done | apply bv_is_ok..].
Qed.
Program Definition bv_not {n} (x : bv n) : bv n := (* SMT: bvnot *)
  bv_of_Z n (Z.lnot (bv_unsigned x)).

Program Definition bv_zero_extend {n} (z : N) (b : bv n) : bv (n + z) := (* SMT: zero_extend *)
  BV _ (bv_unsigned b) _.
Next Obligation.
  intros. apply bv_ok_in_range. rewrite bv_modulus_add. bv_saturate.
  pose proof (bv_modulus_pos z). nia.
Qed.

Program Definition bv_sign_extend {n} (z : N) (b : bv n) : bv (n + z) := (* SMT: sign_extend *)
  bv_of_Z _ (bv_signed b).

(* s is start index and l is length. Note that this is different from
extract in SMTLIB which uses [extract (inclusive upper bound)
(inclusive lower bound)]. The version here is phrased in a way that
makes it impossible to use an upper bound that is lower than the lower
bound. *)
Program Definition bv_extract {n} (s l : N) (b : bv n) : bv l :=
  BV l (Z.land (bv_unsigned b ≫ Z.of_N s) (Z.ones (Z.of_N l))) _.
Next Obligation.
  intros.
  apply bv_ok_in_range.
  apply Z_bounded_iff_bits_nonneg'; [lia | |].
  { apply Z.land_nonneg. left. apply Z.shiftr_nonneg. bv_saturate. lia. }
  intros k ?. rewrite Z.land_spec. apply andb_false_intro2.
  apply Z.ones_spec_high. lia.
Qed.

Program Definition bv_concat {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv (n1 + n2) := (* SMT: concat *)
  BV _ (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)) _.
Next Obligation.
  intros.
  apply bv_ok_in_range.
  apply Z_bounded_iff_bits_nonneg'; [lia | |].
  { apply Z.lor_nonneg. bv_saturate. split; [|lia]. apply Z.shiftl_nonneg. lia. }
  intros k ?. rewrite Z.lor_spec, Z.shiftl_spec; [|lia].
  apply orb_false_intro; (eapply Z_bounded_iff_bits_nonneg; [..|done]); bv_saturate; try lia.
  - apply (Z.lt_le_trans _ (bv_modulus n1)); [lia|]. apply Z.pow_le_mono_r; lia.
  - apply (Z.lt_le_trans _ (bv_modulus n2)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

Definition bv_to_little m n (z : Z) : list (bv n) :=
  (λ b, bv_of_Z n b) <$> Z_to_little m (Z.of_N n) z.

Definition bv_of_little n (bs : list (bv n)) : Z :=
  Z_of_little (Z.of_N n) (bv_unsigned <$> bs).

Lemma bv_to_little_len (m: nat) (n : N) (z : Z) : length (bv_to_little m n z) = m.
Proof.
  unfold bv_to_little.
  rewrite fmap_length.
  apply Z_to_little_len.
Qed.

(** * Lemmas about [bv n] operations *)

(** ** Lemmas about [bv_opp], [bv_add], and [bv_sub] *)
Section add_sub.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_sub_add_opp b1 b2:
    bv_sub b1 b2 = bv_add b1 (bv_opp b2).
  Proof.
    apply bv_eq. unfold bv_sub, bv_add, bv_opp.
    rewrite !bv_of_Z_unsigned. bv_wrap_simplify_solve.
  Qed.

  Lemma bv_add_0 b : bv_add b (bv_of_Z n 0) = b.
  Proof.
    unfold bv_add. rewrite bv_of_Z_unsigned. unfold bv_wrap.  rewrite Zmod_0_l.
    rewrite Z.add_0_r.
    apply bv_unsigned_bv_of_Z.
  Qed.

  Lemma bv_add_assoc b1 b2 b3: bv_add b1 (bv_add b2 b3) = bv_add (bv_add b1 b2) b3.
  Proof.
    unfold bv_add. apply bv_eq. repeat rewrite bv_of_Z_unsigned.
    unfold bv_wrap.
    pose (H:=bv_modulus_pos n).
    rewrite Z.add_mod_idemp_r; [|lia].
    rewrite Z.add_mod_idemp_l; [|lia].
    by rewrite Z.add_assoc.
  Qed.

  Lemma bv_add_signed b1 b2 :
    bv_signed (bv_add b1 b2) = bv_swrap n (bv_signed b1 + bv_signed b2).
  Proof.
    unfold bv_add. rewrite bv_of_Z_signed. unfold bv_signed, bv_swrap. f_equal.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_opp_signed b :
    bv_signed (bv_opp b) = bv_swrap n (- bv_signed b).
  Proof.
    unfold bv_opp. rewrite bv_of_Z_signed. unfold bv_signed, bv_swrap. f_equal.
    bv_wrap_simplify_solve.
  Qed.

  Lemma bv_sub_signed b1 b2 :
    bv_signed (bv_sub b1 b2) = bv_swrap n (bv_signed b1 - bv_signed b2).
  Proof.
    unfold bv_sub. rewrite bv_of_Z_signed. unfold bv_signed, bv_swrap. f_equal.
    bv_wrap_simplify_solve.
  Qed.
End add_sub.

(** ** Lemmas about [bv_mul] *)
Section mul.
  Context {n : N}.
  Implicit Types (b : bv n).

  Lemma bv_mul_signed b1 b2 :
    bv_signed (bv_mul b1 b2) = bv_swrap n (bv_signed b1 * bv_signed b2).
  Proof.
    unfold bv_mul. rewrite bv_of_Z_signed. unfold bv_signed, bv_swrap. f_equal.
    bv_wrap_simplify_solve.
  Qed.
End mul.

(** ** Lemmas about [bv_to_little] and [bv_of_little] *)
Section little.

  Lemma bv_to_litte_unsigned m n z:
    bv_unsigned <$> bv_to_little m n z = Z_to_little m (Z.of_N n) z.
  Proof.
    apply list_eq. intros i. unfold bv_to_little.
    rewrite list_lookup_fmap, list_lookup_fmap.
    destruct (Z_to_little m (Z.of_N n) z !! i) eqn: Heq; [simpl |done].
    rewrite bv_of_Z_small; [done|].
    eapply Z_to_little_bound; [lia|]. by eapply elem_of_list_lookup_2.
  Qed.

  Lemma bv_to_of_little m n bs:
    m = length bs →
    bv_to_little m n (bv_of_little n bs) = bs.
  Proof.
    intros ->. eapply (fmap_inj bv_unsigned). { intros ???. by apply bv_eq. }
    rewrite bv_to_litte_unsigned. apply Z_to_of_little; [by rewrite fmap_length | lia |].
    apply Forall_forall. intros ? [?[->?]]%elem_of_list_fmap_2. apply bv_in_range.
  Qed.

  Lemma bv_of_to_little m n z:
    bv_of_little n (bv_to_little m n z) = z `mod` 2 ^ (m * Z.of_N n).
  Proof. unfold bv_of_little. rewrite bv_to_litte_unsigned. apply Z_of_to_little. lia. Qed.
End little.

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



Section test_automation.
  Context (n : N).
  Implicit Type a : bv n.
  Goal ∀ a n1 n2,
      bv_of_Z n (bv_unsigned (bv_of_Z n (bv_unsigned a + n1)) + n2) =
      bv_of_Z n (bv_unsigned a + (n1 + n2)).
    intros ???.
    apply bv_eq. rewrite !bv_of_Z_unsigned. bv_wrap_simplify_solve.
    all: fail.
  Abort.

  Goal ∀ a n1 n2,
      bv_of_Z n (bv_unsigned (bv_of_Z n (bv_unsigned a + n1 * n1)) + bv_unsigned (bv_of_Z n n2)) =
      bv_of_Z n (bv_unsigned a + (n1 * bv_unsigned (bv_of_Z n n1) + n2)).
    intros ???.
    apply bv_eq. rewrite !bv_of_Z_unsigned. bv_wrap_simplify_solve.
    all: fail.
  Abort.
End test_automation.

(*
(*** Work in progress benchmarks for the automation  *)
(* TODO: Coq.micromega.ZifyClasses does not yet exist in Coq 8.10.2 *)
Require Import Coq.micromega.ZifyClasses.

Global Instance Inj_bv_Z n : InjTyp (bv n) Z :=
  mkinj _ _ bv_unsigned (fun x => 0 ≤ x < bv_modulus n ) (bv_in_range _).

Global Instance Op_bv_unsigned n : UnOp bv_unsigned :=
  { TUOp := fun x => x ; TUOpInj := (fun x : bv n => @eq_refl Z (bv_unsigned x)) }.

Global Instance Op_bv_eq n : BinRel (@eq (bv n)) :=
  {| TR := @eq Z ; TRInj := bv_eq n |}.

Section test_automation.
  Context (n : N).
  Implicit Type a : bv n.
  Implicit Type l : list nat.

  Add InjTyp (Inj_bv_Z n).
  Add UnOp (Op_bv_unsigned n).
  Add BinRel (Op_bv_eq n).

  Goal ∀ a n1 n2,
      bv_of_Z n (bv_unsigned (bv_of_Z n (bv_unsigned a + n1)) + n2) =
      bv_of_Z n (bv_unsigned a + (n1 + n2)).
  Abort.


  Goal ∀ a z, 0 ≤ bv_unsigned a < bv_modulus n * bv_modulus z.
    intros. pose proof (bv_modulus_pos z). nia.
  Abort.

  (* Goal ∀ a, a = a. *)
  (*   zify. *)
  (* Goal ∀ a, bv_of_Z n (bv_unsigned a + 0) = a. *)
  (*   zify. *)
  (*   bv_of_Z n (bv_unsigned a) = a *)
  (* Abort. *)

  Goal ∀ a1 a2,
      bv_unsigned a2 ≤ bv_unsigned a1 →
      a1 ≠ a2 → Z.to_nat (bv_unsigned a1 - bv_unsigned a2) ≠ 0%nat.
    intros ???. rewrite bv_eq. lia.
  Abort.

  Goal ∀ a a0 m, bv_of_Z n (bv_unsigned a + m) = bv_of_Z n (bv_unsigned a0 + m) → a = a0.
  Abort.

  Goal ∀ a m n', bv_of_Z n (bv_unsigned a + m) = bv_of_Z n (bv_unsigned a + n') → m = n'.
  Abort.

  Goal ∀ a1 a2 l,
      bv_unsigned a1 ≤ bv_unsigned a2 ∧ bv_unsigned a2 < bv_unsigned a1 + S (length l) →
      a2 ≠ a1 →
      bv_unsigned (bv_succ a1) ≤ bv_unsigned a2 ∧ bv_unsigned a2 < bv_unsigned (bv_succ a1) + length l.
  Abort.

  Goal ∀ a2 l,
      bv_unsigned a2 + S (length l) < bv_modulus n →
      bv_unsigned (bv_succ a2) + length l < bv_modulus n.
  Abort.

  Goal ∀ a1 a2 l,
      bv_unsigned a2 + S (length l) < bv_modulus n →
      bv_unsigned a1 < bv_unsigned a2 ∨ bv_unsigned a2 + S (length l) ≤ bv_unsigned a1→
      bv_unsigned a1 < bv_unsigned (bv_succ a2) ∨ bv_unsigned (bv_succ a2) + length l ≤ bv_unsigned a1.
  Abort.

  Goal ∀ a1 a2 l,
      bv_unsigned a1 < bv_unsigned a2 ∨ bv_unsigned a2 + S (length l) ≤ bv_unsigned a1 →
      a2 ≠ a1.
  Abort.

  Goal ∀ a1 a2 l,
      bv_unsigned a2 + S (length l) < bv_modulus n →
      a1 ≠ a2 →
      bv_unsigned a2 ≤ bv_unsigned a1 ∧ bv_unsigned a1 < bv_unsigned a2 + S (length l) →
      bv_unsigned (bv_succ a2) ≤ bv_unsigned a1 ∧ bv_unsigned a1 < bv_unsigned (bv_succ a2) + length l.
  Abort.

  Goal ∀ a1 a2 l,
      bv_unsigned a2 + S (length l) < bv_modulus n →
      bv_unsigned a2 ≤ bv_unsigned a1 ∧ bv_unsigned a1 < bv_unsigned a2 + S (length l) →
      a1 ≠ a2 →
      Z.to_nat (bv_unsigned a1 - bv_unsigned (bv_succ a2)) =
      Init.Nat.pred (Z.to_nat (bv_unsigned a1 - bv_unsigned a2)).
  Abort.
End test_automation.
*)
