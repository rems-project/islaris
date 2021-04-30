From Coq Require Export ssreflect.
From stdpp Require Export prelude strings gmap.
From RecordUpdate Require Export RecordSet.
From refframe Require Export module.
From refinedc.lang Require Export base.
Require Export isla.bitvector.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Arguments set _ _ _ _ _ !_ /.

Arguments N.mul : simpl never.

(* TODO: add this to the bitvector library? *)
Global Opaque bv_eq_dec bvn_eq_dec
       bv_0 bv_succ bv_pred
       bv_add bv_sub bv_opp
       bv_mul bv_divu bv_modu
       bv_divs bv_quots bv_mods bv_rems
       bv_shiftl bv_shiftr bv_ashiftr bv_or
       bv_and bv_xor bv_not bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z.


(* This has as better performance characteristic wrt. simpl compared
to list_find since list_find_idx does not contain prod_map. *)
Definition list_find_idx {A} P `{∀ x, Decision (P x)} : list A → option nat :=
  fix go l :=
  match l with
  | [] => None
  | x :: l => if decide (P x) then Some 0%nat else S <$> go l
  end.
Instance: Params (@list_find_idx) 3 := {}.
