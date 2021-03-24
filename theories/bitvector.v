Require Export isla.base.


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
