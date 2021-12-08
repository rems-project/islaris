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

From isla Require Export base.
From refinedc.lithium Require Import Z_bitblast.

Lemma bitblast_bool_to_Z b n:
  Bitblast (bool_to_Z b) n (bool_decide (n = 0) && b).
Proof.
  constructor. destruct b => /=; repeat case_bool_decide;
     subst => //=; rewrite ?Z.bits_0 //; by destruct n.
Qed.
Global Hint Resolve bitblast_bool_to_Z | 10 : bitblast.

Lemma bitblast_bounded_bv_unsigned n (b : bv n):
  BitblastBounded (bv_unsigned b) (Z.of_N n).
Proof. constructor. apply bv_unsigned_in_range. Qed.
Global Hint Resolve bitblast_bounded_bv_unsigned | 15 : bitblast.

Lemma bitblast_bv_wrap z1 n n1 b1:
  Bitblast z1 n b1 →
  Bitblast (bv_wrap n1 z1) n (bool_decide (n < Z.of_N n1) && b1).
Proof.
  move => [<-]. constructor.
  destruct (decide (0 ≤ n)); [by rewrite bv_wrap_spec| rewrite !Z.testbit_neg_r; [|lia..]; btauto].
Qed.
Global Hint Resolve bitblast_bv_wrap | 10 : bitblast.

Lemma bv_extract_concat_later m n1 n2 s l (b1 : bv n1) (b2 : bv n2):
  (n2 ≤ s)%N → (m = n1 + n2)%N →
  bv_extract s l (bv_concat m b1 b2) = bv_extract (s - n2) l b1.
Proof.
  move => ? ->. apply bv_eq.
  rewrite !bv_extract_unsigned bv_concat_unsigned // !bv_wrap_land.
  bitblast. f_equal. lia.
Qed.
Lemma bv_extract_concat_here m n1 n2 s (b1 : bv n1) (b2 : bv n2):
  s = 0%N → (m = n1 + n2)%N →
  bv_extract s n2 (bv_concat m b1 b2) = b2.
Proof.
  move => -> ->. apply bv_eq.
  rewrite !bv_extract_unsigned bv_concat_unsigned // !bv_wrap_land.
  bitblast. f_equal. lia.
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
#[export] Hint Rewrite @bv_concat_0 using done : bv_simplify.
#[export] Hint Rewrite @bv_extract_concat_later @bv_extract_concat_here using lia : bv_simplify.
#[export] Hint Rewrite @bv_extract_bool_to_bv using lia : bv_simplify.
#[export] Hint Rewrite @bv_not_bool_to_bv : bv_simplify.
#[export] Hint Rewrite bool_decide_bool_to_bv_0 bool_decide_bool_to_bv_1 : bv_simplify.

Create HintDb bv_unfold_db discriminated.
Global Hint Constants Opaque : bv_unfold_db.
Global Hint Variables Opaque : bv_unfold_db.
Global Hint Extern 1 (TCFastDone ?P) => (change P; fast_done) : bv_unfold_db.
Global Hint Transparent BvWf andb Is_true Z.ltb Z.leb Z.compare Pos.compare Pos.compare_cont bv_modulus Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul Z.of_N : bv_unfold_db.

Notation bv_suwrap signed := (if signed then bv_swrap else bv_wrap).

Class BvUnfold (n : N) (signed : bool) (wrapped : bool) (b : bv n) (z : Z) := {
    bv_unfold_proof :
      ((if signed then bv_signed else bv_unsigned) b) = (if wrapped then bv_suwrap signed n z else z);
}.
Global Arguments bv_unfold_proof {_ _ _} _ _ {_}.
Global Hint Mode BvUnfold + + + + - : bv_unfold_db.

Definition BV_UNFOLD_BLOCK {A} (x : A) : A := x.

Lemma bv_unfold_end s w n b:
  BvUnfold n s w b ((if s then BV_UNFOLD_BLOCK bv_signed else BV_UNFOLD_BLOCK bv_unsigned) b).
Proof. constructor. unfold BV_UNFOLD_BLOCK. destruct w, s; by rewrite ?bv_wrap_bv_unsigned ?bv_swrap_bv_signed. Qed.
Global Hint Resolve bv_unfold_end | 1000 : bv_unfold_db.
Lemma bv_unfold_BV s w n z Hwf:
  BvUnfold n s w (@BV _ z Hwf) (if w then z else if s then bv_swrap n z else z).
Proof. constructor. destruct w, s; rewrite /bv_unsigned //= bv_wrap_small //. by apply bv_wf_in_range. Qed.
Global Hint Resolve bv_unfold_BV | 10 : bv_unfold_db.
Lemma bv_unfold_Z_to_bv s w n z:
  BvUnfold n s w (Z_to_bv _ z) (if w then z else bv_suwrap s n z).
Proof. constructor. destruct w, s; rewrite ?Z_to_bv_signed ?Z_to_bv_unsigned //=. Qed.
Global Hint Resolve bv_unfold_Z_to_bv | 10 : bv_unfold_db.
Lemma bv_unfold_succ s w n b z:
  BvUnfold n s true b z →
  BvUnfold n s w (bv_succ b) (if w then Z.succ z else bv_suwrap s n (Z.succ z)).
Proof.
  move => [Hz]. constructor.
  destruct w, s; rewrite ?bv_succ_signed ?bv_succ_unsigned ?Hz //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_succ | 10 : bv_unfold_db.
Lemma bv_unfold_pred s w n b z:
  BvUnfold n s true b z →
  BvUnfold n s w (bv_pred b) (if w then Z.pred z else bv_suwrap s n (Z.pred z)).
Proof.
  move => [Hz]. constructor.
  destruct w, s; rewrite ?bv_pred_signed ?bv_pred_unsigned ?Hz //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_pred | 10 : bv_unfold_db.
Lemma bv_unfold_add s w n b1 b2 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_add b1 b2) (if w then z1 + z2 else bv_suwrap s n (z1 + z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_add_signed ?bv_add_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_add | 10 : bv_unfold_db.
Lemma bv_unfold_sub s w n b1 b2 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_sub b1 b2) (if w then z1 - z2 else bv_suwrap s n (z1 - z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_sub_signed ?bv_sub_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_sub | 10 : bv_unfold_db.
Lemma bv_unfold_opp s w n b z:
  BvUnfold n s true b z →
  BvUnfold n s w (bv_opp b) (if w then - z else bv_suwrap s n (- z)).
Proof.
  move => [Hz]. constructor.
  destruct w, s; rewrite ?bv_opp_signed ?bv_opp_unsigned ?Hz //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_opp | 10 : bv_unfold_db.
Lemma bv_unfold_mul s w n b1 b2 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s true b2 z2 →
  BvUnfold n s w (bv_mul b1 b2) (if w then z1 * z2 else bv_suwrap s n (z1 * z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_mul_signed ?bv_mul_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mul | 10 : bv_unfold_db.
Lemma bv_unfold_divu s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_divu b1 b2) (if w then z1 `div` z2 else if s then bv_swrap n (z1 `div` z2) else z1 `div` z2).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_divu_signed ?bv_divu_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_divu b1 b2)). rewrite bv_divu_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_divu | 10 : bv_unfold_db.
Lemma bv_unfold_modu s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_modu b1 b2) (if w then z1 `mod` z2 else if s then bv_swrap n (z1 `mod` z2) else z1 `mod` z2).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_modu_signed ?bv_modu_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_modu b1 b2)). rewrite bv_modu_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_modu | 10 : bv_unfold_db.
Lemma bv_unfold_divs s w n b1 b2 z1 z2:
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_divs b1 b2) (if w then z1 `div` z2 else bv_suwrap s n (z1 `div` z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_divs_signed ?bv_divs_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_divs | 10 : bv_unfold_db.
Lemma bv_unfold_quots s w n b1 b2 z1 z2:
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_quots b1 b2) (if w then z1 `quot` z2 else bv_suwrap s n (z1 `quot` z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_quots_signed ?bv_quots_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_quots | 10 : bv_unfold_db.
Lemma bv_unfold_mods s w n b1 b2 z1 z2:
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_mods b1 b2) (if w then z1 `mod` z2 else bv_suwrap s n (z1 `mod` z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_mods_signed ?bv_mods_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mods | 10 : bv_unfold_db.
Lemma bv_unfold_rems s w n b1 b2 z1 z2:
  BvUnfold n true false b1 z1 →
  BvUnfold n true false b2 z2 →
  BvUnfold n s w (bv_rems b1 b2) (if w then z1 `rem` z2 else bv_suwrap s n (z1 `rem` z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_rems_signed ?bv_rems_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_rems | 10 : bv_unfold_db.
Lemma bv_unfold_shiftl s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_shiftl b1 b2) (if w then z1 ≪ z2 else bv_suwrap s n (z1 ≪ z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_shiftl_signed ?bv_shiftl_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_shiftl | 10 : bv_unfold_db.
Lemma bv_unfold_shiftr s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_shiftr b1 b2) (if w then z1 ≫ z2 else if s then bv_swrap n (z1 ≫ z2) else (z1 ≫ z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_shiftr_signed ?bv_shiftr_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_shiftr b1 b2)). rewrite bv_shiftr_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_shiftr | 10 : bv_unfold_db.
Lemma bv_unfold_ashiftr s w n b1 b2 z1 z2:
  BvUnfold n true false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_ashiftr b1 b2) (if w then z1 ≫ z2 else bv_suwrap s n (z1 ≫ z2)).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_ashiftr_signed ?bv_ashiftr_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_ashiftr | 10 : bv_unfold_db.
Lemma bv_unfold_or s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_or b1 b2) (if w then Z.lor z1 z2 else if s then bv_swrap n (Z.lor z1 z2) else Z.lor z1 z2).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_or_signed ?bv_or_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_or b1 b2)). rewrite bv_or_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_or | 10 : bv_unfold_db.
Lemma bv_unfold_and s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_and b1 b2) (if w then Z.land z1 z2 else if s then bv_swrap n (Z.land z1 z2) else Z.land z1 z2).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_and_signed ?bv_and_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_and b1 b2)). rewrite bv_and_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_and | 10 : bv_unfold_db.
Lemma bv_unfold_xor s w n b1 b2 z1 z2:
  BvUnfold n false false b1 z1 →
  BvUnfold n false false b2 z2 →
  BvUnfold n s w (bv_xor b1 b2) (if w then Z.lxor z1 z2 else if s then bv_swrap n (Z.lxor z1 z2) else Z.lxor z1 z2).
Proof.
  move => [Hz1] [Hz2]. constructor.
  destruct w, s; rewrite ?bv_xor_signed ?bv_xor_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - have := (bv_unsigned_in_range _ (bv_xor b1 b2)). rewrite bv_xor_unsigned => ?. subst.
    by rewrite bv_wrap_small.
Qed.
Global Hint Resolve bv_unfold_xor | 10 : bv_unfold_db.
Lemma bv_unfold_not s w n b z:
  BvUnfold n false false b z →
  BvUnfold n s w (bv_not b) (if w then Z.lnot z else bv_suwrap s n (Z.lnot z)).
Proof.
  move => [Hz]. constructor.
  destruct w, s; rewrite ?bv_not_signed ?bv_not_unsigned ?Hz //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_not | 10 : bv_unfold_db.
Lemma bv_unfold_zero_extend s w n n' b z `{!TCFastDone (n' <=? n = true)%N}:
  BvUnfold n' false false b z →
  BvUnfold n s w (bv_zero_extend n b) (if w then z else if s then bv_swrap n z else z).
Proof.
  move => [Hz]. constructor. unfold TCFastDone in *. rewrite ->?N.leb_le in *.
  destruct w, s; rewrite ?bv_zero_extend_signed ?bv_zero_extend_unsigned ?Hz //=; try bv_wrap_simplify_solve.
  - rewrite -Hz bv_wrap_small //. bv_saturate. pose proof (bv_modulus_le_mono n' n). lia.
Qed.
Global Hint Resolve bv_unfold_zero_extend | 10 : bv_unfold_db.
Lemma bv_unfold_sign_extend s w n n' b z `{!TCFastDone (n' <=? n = true)%N}:
  BvUnfold n' true false b z →
  BvUnfold n s w (bv_sign_extend n b) (if w then z else if s then z else bv_wrap n z).
Proof.
  move => [Hz]. constructor. unfold TCFastDone in *. rewrite ->?N.leb_le in *.
  destruct w, s; rewrite ?bv_sign_extend_signed ?bv_sign_extend_unsigned ?Hz //=; try bv_wrap_simplify_solve.
  - subst. by rewrite -{2}(bv_sign_extend_signed n) // bv_swrap_bv_signed bv_sign_extend_signed.
Qed.
Global Hint Resolve bv_unfold_sign_extend | 10 : bv_unfold_db.
Lemma bv_unfold_extract s w n n' n1 b z:
  BvUnfold n' false false b z →
  BvUnfold n s w (bv_extract n1 n b) (if w then z ≫ Z.of_N n1 else bv_suwrap s n (z ≫ Z.of_N n1)).
Proof.
  move => [Hz]. constructor.
  destruct w, s; rewrite ?bv_extract_signed ?bv_extract_unsigned ?Hz //=; try bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_extract | 10 : bv_unfold_db.
Lemma bv_unfold_concat s w n n1 n2 b1 b2 z1 z2 `{!TCFastDone (n = n1 + n2)%N}:
  BvUnfold n1 false false b1 z1 →
  BvUnfold n2 false false b2 z2 →
  BvUnfold n s w (bv_concat n b1 b2) (if w then Z.lor (z1 ≪ Z.of_N n2) z2 else if s then  bv_swrap n (Z.lor (z1 ≪ Z.of_N n2) z2) else Z.lor (z1 ≪ Z.of_N n2) z2).
Proof.
  move => [Hz1] [Hz2]. constructor. unfold TCFastDone in *.
  destruct w, s; rewrite ?bv_concat_signed ?bv_concat_unsigned ?Hz1 ?Hz2 //=; try bv_wrap_simplify_solve.
  - subst. by rewrite -{2}(bv_concat_unsigned (n1 + n2)) // bv_wrap_bv_unsigned bv_concat_unsigned.
Qed.
Global Hint Resolve bv_unfold_concat | 10 : bv_unfold_db.
Lemma bv_unfold_add_Z s w n b1 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_add_Z b1 z2) (if w then z1 + z2 else bv_suwrap s n (z1 + z2)).
Proof.
  move => [Hz1]. constructor.
  destruct w, s; rewrite ?bv_add_Z_signed ?bv_add_Z_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_add_Z | 10 : bv_unfold_db.
Lemma bv_unfold_sub_Z s w n b1 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_sub_Z b1 z2) (if w then z1 - z2 else bv_suwrap s n (z1 - z2)).
Proof.
  move => [Hz1]. constructor.
  destruct w, s; rewrite ?bv_sub_Z_signed ?bv_sub_Z_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_sub_Z | 10 : bv_unfold_db.
Lemma bv_unfold_mul_Z s w n b1 z1 z2:
  BvUnfold n s true b1 z1 →
  BvUnfold n s w (bv_mul_Z b1 z2) (if w then z1 * z2 else bv_suwrap s n (z1 * z2)).
Proof.
  move => [Hz1]. constructor.
  destruct w, s; rewrite ?bv_mul_Z_signed ?bv_mul_Z_unsigned ?Hz1 ?Hz2 //=; bv_wrap_simplify_solve.
Qed.
Global Hint Resolve bv_unfold_mul_Z | 10 : bv_unfold_db.

Ltac bv_unfold_eq :=
  lazymatch goal with
  | |- @bv_unsigned ?n ?b = ?z =>
      simple notypeclasses refine (@bv_unfold_proof n false false b z _)
  | |- @bv_signed ?n ?b = ?z =>
      simple notypeclasses refine (@bv_unfold_proof n true false b z _)
  end;
  typeclasses eauto with bv_unfold_db.
Ltac bv_unfold :=
  repeat (match goal with
            (* TODO: Detect if there is a bv_wrap around the
            bv_unsigned (like after applying bv_eq_wrapped) *)
          | |- context [@bv_unsigned ?n ?b] =>
              pattern (@bv_unsigned n b);
              simple refine (eq_rec_r _ _ _); [shelve| |bv_unfold_eq]; cbn beta
          | |- context [@bv_signed ?n ?b] =>
              pattern (@bv_signed n b);
              simple refine (eq_rec_r _ _ _); [shelve| |bv_unfold_eq]; cbn beta
          end); unfold BV_UNFOLD_BLOCK.
(*
Ltac bv_unfold_hyp H :=
  repeat (match type of H with
  | context [ @bv_unsigned ?n ?b ] =>
      pattern (@bv_unsigned n b) in H;
      match type of H with
      | ?P ?b =>
          let Hx := fresh in
          (unshelve let x := open_constr:(_) in
                    let xx := open_constr:(_) in
                    pose proof (Hx := @eq_rec _ b P H x xx)); [shelve|bv_unfold_eq|];
          clear H; rename Hx into H; cbn beta in H
      end
  | context [ @bv_signed ?n ?b ] =>
      pattern (@bv_signed n b) in H;
      match type of H with
      | ?P ?b =>
          let Hx := fresh in
          (unshelve let x := open_constr:(_) in
                    let xx := open_constr:(_) in
                    pose proof (Hx := @eq_rec _ b P H x xx)); [shelve|bv_unfold_eq|];
          clear H; rename Hx into H; cbn beta in H
      end
  end); unfold BV_UNFOLD_BLOCK in H.
*)
(* Goal ∀ b : bv 8, ∀ z, *)
(*     bv_signed (bv_succ (bv_succ (bv_zero_extend 64 (bv_add_Z b 5)))) = bv_signed (bv_add b b) *)
(*     → *)
(*       bv_unsigned (bv_add b b) = z. *)
(*   move => ?? H. *)
(*   bv_unfold_hyp H. *)

(** The [bv_unfolded_simplify] database collects rewrite rules that
should be used to simplify the goal after Z is bv_unfolded. *)
Create HintDb bv_unfolded_simplify discriminated.
#[export] Hint Rewrite Z.shiftr_0_r Z.lor_0_r Z.lor_0_l : bv_unfolded_simplify.
#[export] Hint Rewrite Z.land_ones using lia : bv_unfolded_simplify.
#[export] Hint Rewrite bv_wrap_bv_wrap using lia : bv_unfolded_simplify.
#[export] Hint Rewrite Z_to_bv_small using unfold bv_modulus; lia : bv_unfolded_simplify.

(** The [bv_unfolded_to_arith] database collects rewrite rules that
convert bitwise operations to arithmetic operations in preparation for lia. *)
Create HintDb bv_unfolded_to_arith discriminated.
#[export] Hint Rewrite <-Z_opp_lnot : bv_unfolded_to_arith.
#[export] Hint Rewrite Z.shiftl_mul_pow2 Z.shiftr_div_pow2 using lia : bv_unfolded_to_arith.

Ltac reduce_closed_N_tac := idtac.
Ltac reduce_closed_N :=
  idtac;
  reduce_closed_N_tac;
  repeat match goal with
  | |- context [N.add ?a ?b] => progress reduce_closed (N.add a b)
  | H : context [N.add ?a ?b] |- _ => progress reduce_closed (N.add a b)
  end.

Ltac reduce_closed_bv_simplify_tac := idtac.
Ltac reduce_closed_bv_simplify :=
  idtac;
  reduce_closed_bv_simplify_tac;
  (* reduce closed logical operators that lia does not understand *)
  repeat match goal with
  | |- context [Z.lor ?a ?b] => progress reduce_closed (Z.lor a b)
  | H : context [Z.lor ?a ?b] |- _ => progress reduce_closed (Z.lor a b)
  | |- context [Z.land ?a ?b] => progress reduce_closed (Z.land a b)
  | H : context [Z.land ?a ?b] |- _ => progress reduce_closed (Z.land a b)
  | |- context [Z.lxor ?a ?b] => progress reduce_closed (Z.lxor a b)
  | H : context [Z.lxor ?a ?b] |- _ => progress reduce_closed (Z.lxor a b)
  end.

Tactic Notation "bv_simplify" :=
  unLET;
  (* We need to reduce operations on N in indices of bv because
  otherwise lia can get confused (it does not perform unification when
  finding identical subterms). This sometimes leads to problems
  with length of lists of bytes. *)
  reduce_closed_N;
  autorewrite with bv_simplify;
  try apply/bv_eq_wrap;
  bv_unfold;
  (* autorewrite with bv_unfold; *)
  autorewrite with bv_unfolded_simplify.

Tactic Notation "bv_simplify" ident(H) :=
  unLET;
  autorewrite with bv_simplify in H;
  first [ move/bv_eq in H | idtac ];
  tactic bv_unfold in H;
  autorewrite with bv_unfolded_simplify in H.
Tactic Notation "bv_simplify" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify H).

Tactic Notation "bv_simplify_arith" :=
  bv_simplify;
  autorewrite with bv_unfolded_to_arith;
  reduce_closed_bv_simplify.
Tactic Notation "bv_simplify_arith" ident(H) :=
  bv_simplify H;
  autorewrite with bv_unfolded_to_arith in H;
  reduce_closed_bv_simplify.
Tactic Notation "bv_simplify_arith" "select" open_constr(pat) :=
  select pat (fun H => bv_simplify_arith H).

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
Proof. unfold bv_unsigned_land. bitblast. Qed.

Lemma Z_ones_spec' m n : 0 ≤ n → Z.testbit (Z.ones n) m = bool_decide (m < n) && bool_decide (0 ≤ m)%Z.
Proof.
  intros.
  destruct (Z.le_gt_cases 0 m).
  + rewrite Z_ones_spec; [|lia|lia].
    rewrite (bool_decide_eq_true_2 (0 ≤ m)); [|lia].
    by rewrite andb_true_r.
  + rewrite (bool_decide_eq_false_2 (0 ≤ m)); [|lia].
    rewrite Z.testbit_neg_r; [|lia].
    by rewrite andb_false_r.
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

#[export] Hint Rewrite
  Z.bits_0
  Z.lor_0_l Z.lor_0_r
  Z.land_spec Z.lor_spec
  andb_false_l andb_false_r andb_true_l andb_true_r
  orb_false_l orb_false_r orb_true_l orb_true_r : bits_simplify.

#[export] Hint Rewrite
  Z_ones_spec' Z.testbit_neg_r Z.shiftl_spec Z.shiftr_spec Z.lnot_spec using lia : bits_simplify.

#[export] Hint Rewrite <- Z.land_ones using lia : bits_simplify.

Ltac bool_decide_split :=
  repeat match goal with
  | |- context [bool_decide (?a < ?b)] =>
    destruct (Z.lt_ge_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a < b)) | rewrite !(bool_decide_eq_false_2 (a < b)) ]; try lia
  | G : context [bool_decide (?a < ?b)] |- _ =>
    destruct (Z.lt_ge_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a < b)) in G | rewrite !(bool_decide_eq_false_2 (a < b)) in G ]; try lia
  | |- context [bool_decide (?a ≤ ?b)] =>
    destruct (Z.le_gt_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a ≤ b)) | rewrite !(bool_decide_eq_false_2 (a ≤ b)) ]; try lia
  | G : context [bool_decide (?a ≤ ?b)] |- _ =>
    destruct (Z.le_gt_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a ≤ b)) in G | rewrite !(bool_decide_eq_false_2 (a ≤ b)) in G ]; try lia
  end.

Ltac neg_bits_zero :=
  repeat (match goal with |- context [Z.testbit _ ?a] => rewrite (Z.testbit_neg_r _ a); [|lia] end).


Ltac bits_simplify :=
  try apply/bv_eq;
  bv_unfold;
  unfold bv_wrap in *;
  onesify (64%nat);
  repeat match goal with b : bv _ |- _ => match goal with G : bv_unsigned b = _ |- _ => rewrite G; clear G end end;
  repeat match goal with B : bv ?n |- _ => rewrite !(bv_and_ones B) end; unfold bv_unsigned_land;
  try (apply Z.bits_inj_iff';
  let n := fresh "n" in
  let Hn := fresh "Hn" in
  intros n Hn) ;
  repeat (first [
    progress autorewrite with bits_simplify |
    progress bool_decide_split |
    progress neg_bits_zero |
    progress simpl |
    (f_equal; lia)
  ]).

Ltac bitify_hyp H :=
  try (rewrite -> bv_eq in H);
  rewrite <- Z.bits_inj_iff' in H.

Ltac bits_simplify_hyp H :=
  tactic bv_unfold in H;
  unfold bv_wrap in H;
  onesify_hyp (64%nat) H;
  repeat match goal with B : bv ?n |- _ => rewrite !(bv_and_ones B) in H end;
  unfold bv_unsigned_land in H;
  repeat (first [
    progress autorewrite with bits_simplify in H|
    progress bool_decide_split |
    progress simpl in H
  ]).
