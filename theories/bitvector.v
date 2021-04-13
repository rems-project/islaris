Require Export isla.base.

Record bv (n : N) := BV {
  bv_val : Z;
  bv_in_range : -1 < bv_val < 2 ^ Z.of_N n;
  (* TODO: Should we include the above?
  Arguments for:
  - all bit vectors are in normal form by construction and equivalence becomes eq
    - can maybe be mitigated by normalizing aggressively
  Arguments against:
  - Makes constants annoying to write (needs tactics in terms which seems to break stuff in weird ways, e.g typeclass search)
  - n1 = n2 cannot be long solved by done
  *)
}.
Arguments bv_val {_}.

Global Program Instance bv_eq_dec n : EqDecision (bv n) := λ '(BV _ v1 p1) '(BV _ v2 p2),
   match decide (v1 = v2) with
   | left eqv => left _
   | right eqv => right _
   end.
Next Obligation. move => *. subst. f_equal. apply: proof_irrel. Qed.
Next Obligation. move => * [?]. done. Qed.

Lemma bv_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ b1.(bv_val) = b2.(bv_val).
Proof. destruct b1, b2. split => /=; first by case. move => ?. subst. f_equal => //. apply: proof_irrel. Qed.

Coercion bv_val : bv >-> Z.

Definition bv_of_Z_checked (n : N) (z : Z) : option (bv n) :=
  match decide (-1 < z < 2 ^ Z.of_N n) with
  | left Heq => Some (BV n z Heq)
  | right _ => None
  end.

Record bvn := BVN {
  bvn_n : N;
  bvn_val : bv bvn_n;
}.

Lemma bvn_eq (b1 b2 : bvn) :
  b1 = b2 ↔ b1.(bvn_n) = b2.(bvn_n) ∧ b1.(bvn_val).(bv_val) = b2.(bvn_val).(bv_val).
Proof.
  split; [ naive_solver|]. destruct b1, b2 => /= -[??]. subst. f_equal.
  by apply/bv_eq.
Qed.

Global Program Instance bvn_eq_dec : EqDecision bvn := λ '(BVN n1 b1) '(BVN n2 b2),
   match decide (n1 = n2) with
   | left eqv => match decide (b1.(bv_val) = b2.(bv_val)) with
                | left eqb => left _
                | right eqb => right _
                end
   | right eqv => right _
   end.
Next Obligation. move => *. apply/bvn_eq. naive_solver. Qed.
Next Obligation. move => *. apply/bvn_eq. naive_solver. Qed.
Next Obligation. move => *. apply/bvn_eq. naive_solver. Qed.

Definition bvn_to_bv (n : N) (b : bvn) : option (bv n) :=
  match decide (b.(bvn_n) = n) with
  | left eq => Some (eq_rect (bvn_n b) (λ n0 : N, bv n0)
           (bvn_val b) n eq)
  | right _ => None
  end.
Arguments bvn_to_bv !_ !_ /.

Definition bv_to_bvn {n} (b : bv n) : bvn := BVN _ b.
Coercion bv_to_bvn : bv >-> bvn.

Ltac solve_bitvector_eq :=
  try (vm_compute; done);
  lazymatch goal with
  | |- -1 < ?v < 2 ^ ?l =>
    fail "Bitvector constant" v "does not fit into" l "bits"
  end.

Notation "'[BV{' l } v ]" := (BV l v _) (at level 9, format "[BV{ l }  v ]", only printing) : stdpp_scope.
Notation "'[BV{' l } v ]" := (BV l v ltac:(solve_bitvector_eq)) (at level 9, only parsing) : stdpp_scope.
(* Notation "'[BV{' l } v ]" := (BV l v) (at level 9, format "[BV{ l }  v ]") : stdpp_scope. *)

Goal ([BV{10} 3 ] = [BV{10} 5]). Abort.
Fail Goal ([BV{2} 3 ] = [BV{10} 5]).
Goal ([BV{2} 3 ] =@{bvn} [BV{10} 5]). Abort.
Fail Goal ([BV{2} 4 ] = [BV{2} 5]).
Goal bvn_to_bv 2 [BV{2} 3] = Some [BV{2} 3]. done. Abort.


Program Definition bv_zero_extend {n} (z : N) (b : bv n) : bv (n + z) := {|
  bv_val := b.(bv_val);
|}.
Next Obligation. Admitted.

Definition Z_to_signed (bits n : Z) : Z :=
  if bool_decide (2 ^ (bits - 1) ≤ n) then
    n - 2 ^ bits
  else
    n.

Definition Z_to_unsigned (bits n : Z) : Z :=
  if bool_decide (n ≤ 0) then
    n + 2 ^ bits
  else
    n.

Program Definition bv_sign_extend {n} (z : N) (b : bv n) : bv (n + z) := {|
  bv_val := Z_to_unsigned (Z.of_N (n + z)) (Z_to_signed (Z.of_N n) b.(bv_val))
|}.
Next Obligation. Admitted.


(* s is start, l is len *)
Program Definition bv_extract {n} (s l : N) (b : bv n) : bv (l) := {|
  bv_val := Z.land (b.(bv_val) ≫ Z.of_N s) (Z.ones (Z.of_N l));
|}.
Next Obligation. Admitted.

Program Definition bv_add {n} (b1 b2 : bv n) : bv n := {|
  bv_val := b1.(bv_val) + b2.(bv_val) `mod` 2 ^ Z.of_N n;
|}.
Next Obligation. Admitted.

Program Definition bv_or {n} (n1 n2 : bv n) : bv n := {|
  bv_val := Z.lor n1.(bv_val) n2.(bv_val);
|}.
Next Obligation. Admitted.

Program Definition bv_and {n} (n1 n2 : bv n) : bv n := {|
  bv_val := Z.land n1.(bv_val) n2.(bv_val);
|}.
Next Obligation. Admitted.

Program Definition bv_not {n} (b : bv n) : bv n := {|
  bv_val := Z_lunot (Z.of_N n) b.(bv_val);
|}.
Next Obligation. Admitted.

Program Definition bv_concat {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv (n1 + n2) := {|
  (* TODO: Is this the right way around? *)
  bv_val := Z.lor (b1.(bv_val) ≪ Z.of_N n2) b2.(bv_val);
|}.
Next Obligation. Admitted.

Program Definition bv_shr {n} (n1 n2 : bv n) : bv n := {|
  (* TODO: Is this the right way around? *)
  bv_val := (n1.(bv_val) ≫ n2.(bv_val));
|}.
Next Obligation. Admitted.


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
