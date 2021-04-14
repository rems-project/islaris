From stdpp Require Export numbers.
From stdpp Require Import countable.
From stdpp Require Import options.

Local Open Scope Z_scope.

Lemma pos_bounded_iff_bits k n :
  (0 ≤ k → 0 ≤ n → n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false)%Z.
Proof.
  intros.
  destruct (decide (n = 0)) as [->|].
  - setoid_rewrite Z.bits_0. split; [done|]. intros. by apply Z.pow_pos_nonneg.
  - split.
    + intros Hb%Z.log2_lt_pow2 l Hl; [| lia]. apply Z.bits_above_log2; lia.
    + intros Hl.
      destruct (decide (n < 2^k)%Z); [done|].
      assert (Z.testbit n (Z.log2 n) = false) as Hbit.
      { apply Hl, Z.log2_le_pow2; lia. }
      rewrite Z.bit_log2 in Hbit; [done| lia].
Qed.


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

Lemma bv_ok_bitwise_op {n} op bop n1 n2 :
  (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
  (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
  bop false false = false →
  bv_ok n n1 → bv_ok n n2 → bv_ok n (op n1 n2).
Proof.
  intros Hbits Hnonneg Hop [? Hok1]%bv_ok_in_range [? Hok2]%bv_ok_in_range. apply bv_ok_in_range.
  split; [lia|].
  apply pos_bounded_iff_bits; [lia..|]. intros l ?.
  eapply pos_bounded_iff_bits in Hok1;[|try done; lia..].
  eapply pos_bounded_iff_bits in Hok2;[|try done; lia..].
  by rewrite Hbits, Hok1, Hok2.
Qed.

(*** Definition of [bv n] *)
Record bv (n : N) := BV {
  bv_unsigned : Z;
  bv_is_ok : bv_ok n bv_unsigned;
}.
Arguments bv_unsigned {_}.
Arguments bv_is_ok {_}.

Definition bv_signed {n} (b : bv n) := bv_swrap n (bv_unsigned b).

Lemma bv_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ b1.(bv_unsigned) = b2.(bv_unsigned).
Proof. destruct b1, b2. split; simpl; [ naive_solver|]. intros. subst. f_equal. apply proof_irrel. Qed.

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

Program Definition bv_of_Z (n : N) (z : Z) : bv n := {|
  bv_unsigned := bv_wrap n z;
|}.
Next Obligation. apply bv_wrap_ok. Qed.
Arguments bv_of_Z : simpl never.
Global Opaque bv_of_Z.

Lemma bv_in_range n (b : bv n):
  0 ≤ bv_unsigned b < bv_modulus n.
Proof. apply bv_ok_in_range. apply bv_is_ok. Qed.

(*** Notation for [bv n] *)
Ltac solve_bitvector_eq :=
  try (vm_compute; done);
  lazymatch goal with
  | |- -1 < ?v < 2 ^ ?l =>
    fail "Bitvector constant" v "does not fit into" l "bits"
  end.

Notation "'[BV{' l } v ]" := (BV l v _) (at level 9, format "[BV{ l }  v ]", only printing) : stdpp_scope.
(* TODO: This notation breaks when used in gmap notations. Why? *)
Notation "'[BV{' l } v ]" := (BV l v ltac:(solve_bitvector_eq)) (at level 9, only parsing) : stdpp_scope.

(*** Automation *)
(* From Program.Tactics *)
Ltac add_hypothesis H' p :=
  match type of p with
    ?X =>
    match goal with
      | [ H : X |- _ ] => fail 1
      | _ => set (H':=p) ; try (change p with H') ; clearbody H'
    end
  end.
Ltac bv_saturate :=
  repeat match goal with
         | b : bv _ |- _ =>
           let H := fresh in
           add_hypothesis H (bv_in_range _ b)
         end.


(*** Operations on [bv n] *)

Definition bv_add {n} (x y : bv n) : bv n := (* SMT: bvadd *)
  bv_of_Z n (Z.add (bv_unsigned x) (bv_unsigned y)).
Definition bv_sub {n} (x y : bv n) : bv n := (* SMT: bvsub *)
  bv_of_Z n (Z.sub (bv_unsigned x) (bv_unsigned y)).
Definition bv_opp {n} (x y : bv n) : bv n := (* SMT: bvneg *)
  bv_of_Z n (Z.opp (bv_unsigned x)).

Definition bv_mul {n} (x y : bv n) : bv n := (* SMT: bvmul *)
  bv_of_Z n (Z.mul (bv_unsigned x) (bv_unsigned y)).
Definition bv_divu {n} (x y : bv n) : bv n := (* SMT: bvudiv *)
  bv_of_Z n (Z.div (bv_unsigned x) (bv_unsigned y)).
Definition bv_modu {n} (x y : bv n) : bv n := (* SMT: bvurem *)
  bv_of_Z n (Z.modulo (bv_unsigned x) (bv_unsigned y)).
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
Definition bv_shiftr {n} (x y : bv n) : bv n := (* SMT: bvlshr *)
  bv_of_Z n (Z.shiftr (bv_unsigned x) (bv_unsigned y)).
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
  split; [lia|]. apply pos_bounded_iff_bits; [lia.. |].
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
  split; [lia|]. apply pos_bounded_iff_bits; [lia.. |].
  intros k ?. rewrite Z.lor_spec, Z.shiftl_spec; [|lia].
  apply orb_false_intro; (eapply pos_bounded_iff_bits; [..|done]); bv_saturate; try lia.
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
Arguments bvn_to_bv !_ !_ /.

Definition bv_to_bvn {n} (b : bv n) : bvn := BVN _ b.
Coercion bv_to_bvn : bv >-> bvn.

(*** [tests] *)
Section test.
Goal ([BV{10} 3 ] = [BV{10} 5]). Abort.
Fail Goal ([BV{2} 3 ] = [BV{10} 5]).
Goal ([BV{2} 3 ] =@{bvn} [BV{10} 5]). Abort.
Fail Goal ([BV{2} 4 ] = [BV{2} 5]).
Goal bvn_to_bv 2 [BV{2} 3] = Some [BV{2} 3]. done. Abort.
End test.

(*
(*** Old definition of bit vectors *)

Record bv := BV {
  bv_len : Z;
  bv_val : Z;
  (* TODO: Should we include the following?
  bv_in_range : -1 < bv_val < 2 ^ bv_len;
  Arguments for:
  - all bit vectors are in normal form by construction and equivalence becomes eq
    - can maybe be mitigated by normalizing aggressively
  Arguments against:
  - Makes constants annoying to write (needs tactics in terms which seems to break stuff in weird ways, e.g typeclass search)
  - n1 = n2 cannot be long solved by done
  *)
}.

Global Instance bv_eq_dec : EqDecision bv.
Proof. solve_decision. Defined.

Definition bv_normalize (n : bv) : bv := {|
  bv_len := n.(bv_len);
  bv_val := n.(bv_val) `mod` 2 ^ n.(bv_len);
|}.

Definition bv_is_normal (n : bv) : Prop := n = bv_normalize n.

(* Ltac solve_bitvector_eq := *)
(*   try (vm_compute; done); *)
(*   lazymatch goal with *)
(*   | |- -1 < ?v < 2 ^ ?l => *)
(*     fail "Bitvector constant" v "does not fit into" l "bits" *)
(*   end. *)

(* Notation "'[BV{' l } v ]" := (BV l v _) (at level 9, format "[BV{ l }  v ]", only printing) : stdpp_scope. *)
(* Notation "'[BV{' l } v ]" := (BV l v ltac:(solve_bitvector_eq)) (at level 9, only parsing) : stdpp_scope. *)
Notation "'[BV{' l } v ]" := (BV l v) (at level 9, format "[BV{ l }  v ]") : stdpp_scope.

(* Goal ([BV{2} 3 ] = [BV{10} 5]). Abort. *)
(* Fail Goal ([BV{2} 4 ] = [BV{10} 5]).  *)

(* Assumes z ≥ 0 *)
Program Definition bv_zero_extend (z : Z) (n : bv) : bv := {|
  bv_len := n.(bv_len) + (z `max` 0);
  bv_val := n.(bv_val);
|}.

(* Assumes z ≥ 0 *)
Definition bv_sign_extend (z : Z) (n : bv) : bv.
Admitted.


(* Assumes l < u *)
Program Definition bv_extract (u l : Z) (n : bv) : bv := {|
  bv_len := u + 1 - l;
  bv_val := (n.(bv_val) ≫ l) `mod` 2 ^ (u + 1 - l);
|}.

(* Assumes n1.(bv_len) = n2.(bv_len) *)
Program Definition bv_add (n1 n2 : bv) : bv := {|
  bv_len := n1.(bv_len);
  bv_val := n1.(bv_val) + n2.(bv_val);
|}.

(* Assumes n1.(bv_len) = n2.(bv_len) *)
Program Definition bv_or (n1 n2 : bv) : bv := {|
  bv_len := n1.(bv_len);
  bv_val := Z.lor n1.(bv_val) n2.(bv_val);
|}.

(* Assumes n1.(bv_len) = n2.(bv_len) *)
Program Definition bv_and (n1 n2 : bv) : bv := {|
  bv_len := n1.(bv_len);
  bv_val := Z.land n1.(bv_val) n2.(bv_val);
|}.

Program Definition bv_not (n : bv) : bv := {|
  bv_len := n.(bv_len);
  bv_val := Z.lnot n.(bv_val) `mod` 2 ^ n.(bv_len);
|}.

Program Definition bv_concat (n1 n2 : bv) : bv := {|
  bv_len := n1.(bv_len) + n2.(bv_len);
  (* TODO: Is this the right way around? *)
  bv_val := Z.lor (n1.(bv_val) ≪ n2.(bv_len)) n2.(bv_val);
|}.

Program Definition bv_shr (n1 n2 : bv) : bv := {|
  bv_len := n1.(bv_len);
  (* TODO: Is this the right way around? *)
  bv_val := (n1.(bv_val) ≫ n2.(bv_val));
|}.
*)
