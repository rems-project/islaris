From isla Require Export base.
From refinedc.lithium Require Import Z_bitblast.

Typeclasses Opaque Z_to_bv
       bv_0 bv_succ bv_pred
       bv_add bv_sub bv_opp
       bv_mul bv_divu bv_modu
       bv_divs bv_quots bv_mods bv_rems
       bv_shiftl bv_shiftr bv_ashiftr bv_or
       bv_and bv_xor bv_not bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z
       bool_to_bv.
Global Opaque Z_to_bv
       bv_0 bv_succ bv_pred
       bv_add bv_sub bv_opp
       bv_mul bv_divu bv_modu
       bv_divs bv_quots bv_mods bv_rems
       bv_shiftl bv_shiftr bv_ashiftr bv_or
       bv_and bv_xor bv_not bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z
       bool_to_bv.

Lemma bool_to_Z_Z_of_bool:
  bool_to_Z = Z_of_bool.
Proof. done. Qed.

Hint Rewrite bv_unsigned_spec_high using lia : rewrite_bits_db.

Lemma bv_extract_concat_later m n1 n2 s l (b1 : bv n1) (b2 : bv n2):
  (n2 ≤ s)%N → (m = n1 + n2)%N →
  bv_extract s l (bv_concat m b1 b2) = bv_extract (s - n2) l b1.
Proof.
  move => ? ->. apply bv_eq.
  rewrite !bv_extract_unsigned bv_concat_unsigned // !bv_wrap_land.
  bitblast.
Qed.
Lemma bv_extract_concat_here m n1 n2 s (b1 : bv n1) (b2 : bv n2):
  s = 0%N → (m = n1 + n2)%N →
  bv_extract s n2 (bv_concat m b1 b2) = b2.
Proof.
  move => -> ->. apply bv_eq.
  rewrite !bv_extract_unsigned bv_concat_unsigned // !bv_wrap_land.
  bitblast.
Qed.

Lemma bool_decide_bool_to_bv_0 b:
  (bool_decide (bv_unsigned (bool_to_bv 1 b) = 0)) = negb b.
Proof. by destruct b. Qed.
Lemma bool_decide_bool_to_bv_1 b:
  (bool_decide (bv_unsigned (bool_to_bv 1 b) = 1)) = b.
Proof. by destruct b. Qed.

(** The [bv_simplify] database collects rewrite rules that rewrite
bitvectors into other bitvectors. *)
Create HintDb bv_simplify discriminated.
Hint Rewrite @bv_concat_0 using done : bv_simplify.
Hint Rewrite @bv_extract_concat_later @bv_extract_concat_here using lia : bv_simplify.
Hint Rewrite @bv_extract_bool_to_bv using lia : bv_simplify.
Hint Rewrite @bv_not_bool_to_bv : bv_simplify.
Hint Rewrite bool_decide_bool_to_bv_0 bool_decide_bool_to_bv_1 : bv_simplify.

(** The [bv_unfold] database contains rewrite rules that propagate
bv_unsigned and bv_signed and unfold the bitvector definitions. *)
Create HintDb bv_unfold discriminated.
Lemma bv_unsigned_BV n z Heq:
  bv_unsigned (BV n z Heq) = z.
Proof. done. Qed.
Lemma bv_signed_BV n z Heq:
  bv_signed (BV n z Heq) = bv_swrap n z.
Proof. done. Qed.

(* Rules without sideconditions *)
Hint Rewrite
     @bv_succ_unsigned @bv_succ_signed
     @bv_pred_unsigned @bv_pred_signed
     @bv_add_unsigned @bv_add_signed
     @bv_sub_unsigned @bv_sub_signed
     @bv_opp_unsigned @bv_opp_signed
     @bv_mul_unsigned @bv_mul_signed
     @bv_divu_unsigned @bv_divu_signed
     @bv_modu_unsigned @bv_modu_signed
     @bv_divs_unsigned @bv_divs_signed
     @bv_quots_unsigned @bv_quots_signed
     @bv_mods_unsigned @bv_mods_signed
     @bv_rems_unsigned @bv_rems_signed
     @bv_shiftl_unsigned @bv_shiftl_signed
     @bv_shiftr_unsigned @bv_shiftr_signed
     @bv_ashiftr_unsigned @bv_ashiftr_signed
     @bv_or_unsigned @bv_or_signed
     @bv_and_unsigned @bv_and_signed
     @bv_xor_unsigned @bv_xor_signed
     @bv_not_unsigned @bv_not_signed
     @bv_zero_extend_signed
     @bv_sign_extend_unsigned
     @bv_extract_unsigned @bv_extract_signed
     @bv_add_Z_unsigned @bv_add_Z_signed
     @bv_sub_Z_unsigned @bv_sub_Z_signed
     @bv_mul_Z_unsigned @bv_mul_Z_signed
     @bv_unsigned_BV @bv_signed_BV
  : bv_unfold.

(* Rules with sideconditions *)
Hint Rewrite
     @bv_zero_extend_unsigned @bv_sign_extend_signed
     @bv_concat_unsigned
     using lia
  : bv_unfold.

(** The [bv_unfolded_simplify] database collects rewrite rules that
should be used to simplify the goal after Z is bv_unfolded. *)
Create HintDb bv_unfolded_simplify discriminated.
Hint Rewrite Z.shiftr_0_r Z.lor_0_r Z.lor_0_l : bv_unfolded_simplify.
Hint Rewrite Z.land_ones using lia : bv_unfolded_simplify.
Hint Rewrite bv_wrap_bv_wrap using lia : bv_unfolded_simplify.

(** The [bv_unfolded_to_arith] database collects rewrite rules that
convert bitwise operations to arithmetic operations in preparation for lia. *)
Create HintDb bv_unfolded_to_arith discriminated.
Hint Rewrite Z_lnot_opp : bv_unfolded_to_arith.
Hint Rewrite Z.shiftl_mul_pow2 Z.shiftr_div_pow2 using lia : bv_unfolded_to_arith.

Ltac reduce_closed_N_tac := idtac.
Ltac reduce_closed_N :=
  idtac;
  reduce_closed_N_tac;
  repeat match goal with
  | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
  | H : context [N.add ?a ?b] |- _ => progress reduce_closed (N.add a b)
  end.


Ltac bv_simplify :=
  unLET;
  (* We need to reduce operations on N in indices of bv because
  otherwise lia can get confused (it does not perform unification when
  finding identical subterms). This sometimes leads to problems
  with length of lists of bytes. *)
  reduce_closed_N;
  autorewrite with bv_simplify;
  try apply/bv_eq_wrap;
  autorewrite with bv_unfold;
  autorewrite with bv_unfolded_simplify.

Ltac bv_simplify_hyp H :=
  unLET;
  autorewrite with bv_simplify in H;
  first [ move/bv_eq in H | idtac ];
  autorewrite with bv_unfold in H;
  autorewrite with bv_unfolded_simplify in H.
Tactic Notation "bv_simplify_hyp" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify_hyp H).

Ltac bv_simplify_arith :=
  bv_simplify;
  autorewrite with bv_unfolded_to_arith.
Ltac bv_simplify_arith_hyp H :=
  bv_simplify_hyp H;
  autorewrite with bv_unfolded_to_arith in H.
Tactic Notation "bv_simplify_arith_hyp" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify_arith_hyp H).

Ltac bv_solve_unfold_tac := idtac.

(* TODO: upstream *)
Ltac bv_saturate_unsigned :=
  repeat match goal with b : bv _ |- _ => first [
     clear b |
     learn_hyp (bv_unsigned_in_range _ b)
  ] end.

Ltac bv_solve :=
  bv_simplify_arith;
  (* try lazymatch goal with *)
  (* | |- bv_wrap _ _ = bv_wrap _ _ => f_equal *)
  (* end; *)
  (* we unfold signed so we just need to saturate unsigned *)
  bv_saturate_unsigned;
  bv_solve_unfold_tac;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned in *;
  simpl;
  lia.

Class BvSolve (P : Prop) : Prop := bv_solve_proof : P.
Global Hint Extern 1 (BvSolve ?P) => (change P; bv_solve) : typeclass_instances.

Definition bv_unsigned_land {n} (v : bv n) := Z.land (bv_unsigned v) (Z.ones (Z.of_N n)).

Lemma bv_and_ones {n} (v : bv n) : bv_unsigned v = bv_unsigned_land v.
Proof.
  unfold bv_unsigned_land.
  rewrite Z.land_ones; [|lia].
  symmetry.
  apply Z.mod_small.
  destruct v as [x wf].
  unfold bitvector.bv_wf, bv_modulus in wf.
  unfold bv_unsigned.
  lia.
Qed.

Ltac onesify n :=
  lazymatch n with
  | O => idtac
  | S ?n' => 
    let m := eval vm_compute in (Z.of_nat n) in
    let x := eval vm_compute in (Z.ones m) in
    change x with (Z.ones m);
    onesify n'
  end.

Ltac onesify_hyp n H :=
  lazymatch n with
  | O => idtac
  | S ?n' => 
    let m := eval vm_compute in (Z.of_nat n) in
    let x := eval vm_compute in (Z.ones m) in
    change x with (Z.ones m) in H;
    onesify_hyp n' H
  end.

Hint Rewrite
  Z.bits_0
  Z.lor_0_l Z.lor_0_r
  Z.land_spec Z.lor_spec
  andb_false_l andb_false_r andb_true_l andb_true_r
  orb_false_l orb_false_r orb_true_l orb_true_r : bits_simplify.

Hint Rewrite
  Z_ones_spec Z.testbit_neg_r Z.shiftl_spec Z.shiftr_spec Z.lnot_spec using lia : bits_simplify.

Hint Rewrite <- Z.land_ones using lia : bits_simplify.

Ltac bool_decide_split :=
  repeat match goal with 
  | |- context [bool_decide (?a < ?b)] => 
    destruct (Z.lt_ge_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a < b)) | rewrite !(bool_decide_eq_false_2 (a < b)) ]; try lia
  | G : context [bool_decide (?a < ?b)] |- _ =>
    destruct (Z.lt_ge_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a < b)) in G | rewrite !(bool_decide_eq_false_2 (a < b)) in G ]; try lia
  end.

Ltac neg_bits_zero :=
  repeat (match goal with |- context [Z.testbit _ ?a] => rewrite (Z.testbit_neg_r _ a); [|lia] end).


Ltac bits_simplify :=
  apply bv_eq;
  autorewrite with bv_unfold;
  unfold bv_wrap in *;
  onesify (64%nat);
  repeat match goal with b : bv _ |- _ => match goal with G : bv_unsigned b = _ |- _ => rewrite G; clear G end end;
  repeat match goal with B : bv ?n |- _ => rewrite !(bv_and_ones B) end; unfold bv_unsigned_land;
  apply Z.bits_inj_iff';
  let n := fresh "n" in
  let Hn := fresh "Hn" in
  intros n Hn;
  repeat (first [
    progress autorewrite with bits_simplify | 
    progress bool_decide_split |
    progress neg_bits_zero |
    progress simpl
  ]).

Ltac bitify_hyp H :=
  rewrite -> bv_eq in H;
  rewrite <- Z.bits_inj_iff' in H.

Ltac bits_simplify_hyp H :=
  autorewrite with bv_unfold in H;
  unfold bv_wrap in H;
  onesify_hyp (64%nat) H;
  repeat match goal with B : bv ?n |- _ => rewrite !(bv_and_ones B) in H end;
  unfold bv_unsigned_land in H;
  repeat (first [
    progress autorewrite with bits_simplify in H| 
    progress bool_decide_split |
    progress simpl in H
  ]).