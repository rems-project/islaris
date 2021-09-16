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
       bv_add_Z bv_sub_Z bv_mul_Z.
Global Opaque Z_to_bv
       bv_0 bv_succ bv_pred
       bv_add bv_sub bv_opp
       bv_mul bv_divu bv_modu
       bv_divs bv_quots bv_mods bv_rems
       bv_shiftl bv_shiftr bv_ashiftr bv_or
       bv_and bv_xor bv_not bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z.

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

(** The [bv_simplify] database collects rewrite rules that rewrite
bitvectors into other bitvectors. *)
Create HintDb bv_simplify discriminated.
Hint Rewrite @bv_concat_0 using done : bv_simplify.
Hint Rewrite @bv_extract_concat_later @bv_extract_concat_here using lia : bv_simplify.

(* These rules are also useful for general simplification. *)
Hint Rewrite @bv_extract_concat_later @bv_extract_concat_here using lia : lithium_rewrite.

(** The [bv_unfold] database contains rewrite rules that propagate
bv_unsigned and bv_signed and unfold the bitvector definitions. *)
Create HintDb bv_unfold discriminated.
Lemma bv_unsigned_BV n z Heq:
  bv_unsigned (BV n z Heq) = z.
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
     @bv_unsigned_BV
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
  try apply bv_eq_wrap;
  autorewrite with bv_unfold;
  autorewrite with bv_unfolded_simplify.

Ltac bv_simplify_hyp H :=
  unLET;
  autorewrite with bv_simplify in H;
  first [ apply bv_eq in H | apply bv_neq in H | idtac ];
  autorewrite with bv_unfold in H;
  autorewrite with bv_unfolded_simplify in H.
Tactic Notation "bv_simplify_hyp" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify_hyp H).

Ltac bv_solve_unfold_tac := idtac.

Ltac bv_solve :=
  bv_simplify;
  (* try lazymatch goal with *)
  (* | |- bv_wrap _ _ = bv_wrap _ _ => f_equal *)
  (* end; *)
  bv_saturate;
  bv_solve_unfold_tac;
  unfold bv_wrap, bv_modulus, bv_unsigned in *;
  simpl;
  lia.
