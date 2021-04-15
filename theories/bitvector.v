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

Tactic Notation "learn_hyp" constr(p) "as" ident(H') :=
  let P := type of p in
  match goal with
  | H : P |- _ => fail 1
  | _ => pose proof p as H'
  end.
Tactic Notation "learn_hyp" constr(p) :=
  let H := fresh in learn_hyp p as H.


(*** Preliminary definitions *)
Definition bv_modulus (n : N) : Z := 2 ^ (Z.of_N n).
Definition bv_half_modulus (n : N) : Z := 2 ^ (Z.of_N (n - 1)).
Definition bv_wrap (n : N) (z : Z) : Z := z `mod` bv_modulus n.
Definition bv_swrap (n : N) (z : Z) : Z := bv_wrap n (z + bv_half_modulus n) - bv_half_modulus n.
Definition bv_ok (n : N) (z : Z) : Prop := -1 < z < bv_modulus n.

Lemma bv_modulus_pos n :
  0 < bv_modulus n.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

Lemma bv_modulus_add n1 n2 :
  bv_modulus (n1 + n2) = bv_modulus n1 * bv_modulus n2.
Proof. unfold bv_modulus. rewrite N2Z.inj_add. eapply Z.pow_add_r; lia. Qed.

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

Lemma bv_wrap_elim n z :
  0 ≤ z < bv_modulus n → bv_wrap n z = z.
Proof. intros. by apply Z.mod_small. Qed.

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

(*** Definition of [bv n] *)
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

Global Arguments bv_of_Z : simpl never.
Global Opaque bv_of_Z.

Lemma bv_of_Z_elim n z:
  0 ≤ z < bv_modulus n →
  bv_unsigned (bv_of_Z n z) = z.
Proof. rewrite bv_of_Z_unsigned. apply bv_wrap_elim. Qed.

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
  apply bv_eq in Hz. rewrite !bv_of_Z_elim in Hz; lia.
Qed.
Next Obligation.
  intros. apply elem_of_list_lookup. eexists (Z.to_nat (bv_unsigned x)).
  rewrite list_lookup_fmap. apply fmap_Some. eexists _.
  pose proof (bv_in_range _ x). split.
  - apply lookup_seqZ. split; [done|]. rewrite Z2Nat.id; lia.
  - apply bv_eq. rewrite bv_of_Z_elim; rewrite Z2Nat.id; lia.
Qed.


(*** Notation for [bv n] *)
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

(*** Automation *)
Ltac bv_saturate :=
  repeat match goal with | b : bv _ |- _ => learn_hyp (bv_in_range _ b) end.


(*** Operations on [bv n] *)
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
Definition bv_opp {n} (x y : bv n) : bv n := (* SMT: bvneg *)
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
(inclusive lower bound)] *)
Program Definition bv_extract {n} (s l : N) (b : bv n) : bv l :=
  BV l (Z.land (bv_unsigned b ≫ Z.of_N s) (Z.ones (Z.of_N l))) _.
Next Obligation.
  intros.
  apply bv_ok_in_range.
  assert (0 ≤ Z.land (bv_unsigned b ≫ Z.of_N s) (Z.ones (Z.of_N l))).
  { apply Z.land_nonneg. left. apply Z.shiftr_nonneg. bv_saturate. lia. }
  split; [lia|]. apply Z_bounded_iff_bits_nonneg; [lia.. |].
  intros k ?. rewrite Z.land_spec. apply andb_false_intro2.
  apply Z.ones_spec_high. lia.
Qed.

Program Definition bv_concat {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv (n1 + n2) := (* SMT: concat *)
  BV _ (Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)) _.
Next Obligation.
  intros.
  apply bv_ok_in_range.
  assert (0 ≤ Z.lor (bv_unsigned b1 ≪ Z.of_N n2) (bv_unsigned b2)).
  { apply Z.lor_nonneg. bv_saturate. split; [|lia]. apply Z.shiftl_nonneg. lia. }
  split; [lia|]. apply Z_bounded_iff_bits_nonneg; [lia.. |].
  intros k ?. rewrite Z.lor_spec, Z.shiftl_spec; [|lia].
  apply orb_false_intro; (eapply Z_bounded_iff_bits_nonneg; [..|done]); bv_saturate; try lia.
  - apply (Z.lt_le_trans _ (bv_modulus n1)); [lia|]. apply Z.pow_le_mono_r; lia.
  - apply (Z.lt_le_trans _ (bv_modulus n2)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.

(*** [bvn] *)
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

(*** tests *)
Section test.
Goal ([BV{10} 3 ] = [BV{10} 5]). Abort.
Fail Goal ([BV{2} 3 ] = [BV{10} 5]).
Goal ([BV{2} 3 ] =@{bvn} [BV{10} 5]). Abort.
Fail Goal ([BV{2} 4 ] = [BV{2} 5]).
Goal bvn_to_bv 2 [BV{2} 3] = Some [BV{2} 3]. done. Abort.
End test.

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
