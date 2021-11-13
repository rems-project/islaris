Require Import isla.aarch64.aarch64.
From isla.instructions.rbit Require Import instrs.

Tactic Notation "select" "subterm" open_constr(pat) tactic3(tac) :=
  match goal with
  | |- context H [?x]       => unify x pat; tac x
  | _ : context H [?x] |- _ => unify x pat; tac x
  end.

Tactic Notation "reduce" "pattern" open_constr(pat) :=
  repeat select subterm pat (fun x => reduce_closed x).

(* TODO: This tactic is quite inefficient (it calls unification for
every subterm in the goal and hyps). Can we do something about this? *)
Tactic Notation "select" "closed" "subterm" "of" "type" constr(T) tactic3(tac) :=
  match goal with
  | |- context H [?x]       => let ty := type of x in unify ty T; check_closed x; tac x
  | _ : context H [?x] |- _ => let ty := type of x in unify ty T; check_closed x; tac x
  end.

Ltac evalZ :=
  repeat select closed subterm of type Z (fun x => progress reduce_closed x).

Lemma bv_wrap_wrap {N} b : bv_wrap N (bv_wrap N b) = bv_wrap N b.
Proof. by rewrite /bv_wrap Zmod_mod. Qed.

Lemma tac_lor_eq a1 b1 a2 b2: a1 = a2 → b1 = b2 → Z.lor a1 b1 = Z.lor a2 b2.
Proof. move => -> -> //. Qed.

Lemma simplify_stuff (b n : bv 64) :
  bv_extract 0 1 (bv_shiftr b n) = bool_to_bv 1 (Z.testbit (bv_unsigned b) (bv_unsigned n)).
Proof.
Admitted.

Lemma simplify_more {N} (b : bv N) (n k : Z):
  0 ≤ n →
  0 ≤ k →
  k + n = Z.of_N N - 1 →
  bv_wrap N (bv_wrap N (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b) k))) ≪ n) =
  bool_to_Z (Z.testbit (bv_unsigned b) k) ≪ n.
Proof.
  move => ?? HN. rewrite /bv_wrap. generalize (bv_unsigned b) => z. clear b.
  rewrite /bv_modulus. evalZ.
  assert (0 ≤ Z.of_N N) as HN0 by lia. revert HN0 HN. generalize (Z.of_N N) => Z. clear N.
  move => ??. bitblast.
  all: rewrite ?Zmod_0_l ?Z.shiftl_0_l ?Zmod_0_l ?Z.testbit_0_l //.
  - rewrite Z.testbit_mod_pow2; last lia.
    rewrite Z.shiftl_spec; last lia.
    rewrite Z.testbit_mod_pow2; last lia.
    assert (Z.testbit _ (i - n) = false) as ->; last by rewrite !andb_false_r.
    destruct (Z.testbit z k) => /=; evalZ; last by rewrite Z.testbit_0_l.
    by destruct (i - n).
  - rewrite Z.testbit_mod_pow2; last lia.
    rewrite Z.shiftl_spec; last lia.
    rewrite Z.testbit_mod_pow2; last lia.
    destruct (Z.testbit z k) eqn:Heq => /=; last first.
    { rewrite Z.testbit_0_l !andb_false_r //. }
    assert (1 `mod` 2 = 1) as -> by lia.
    destruct (decide (i < Z ∧ i - n < Z)) as [[Hlt1 Hlt2]|?].
    + apply Z.ltb_lt in Hlt1. apply Z.ltb_lt in Hlt2.
      rewrite Hlt1 Hlt2 //.
    + assert (Z.testbit 1 (i - n) = false) as ->; last by rewrite !andb_false_r.
      destruct (i - n) eqn:? => //. exfalso. apply n0.
      split; last lia. lia.
Qed.

Fixpoint rbit_Z_aux (N : nat) (z : Z) (n : nat) : Z :=
  match n with
  | O   => 0
  | S n => Z.lor (rbit_Z_aux N z n) ((bool_to_Z (Z.testbit z n)) ≪ (N - S n)%nat)
  end.

Definition rbit_Z N z := rbit_Z_aux N z N.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Definition rbit_spec (stack_size : Z) : iProp Σ := (
  c_call stack_size (λ args sp RET,
    ∃ (x : Z) P,
    ⌜bv_unsigned (args !!! 0%nat) = x⌝ ∗
    P ∗
    RET (λ rets,
      ⌜bv_unsigned (rets !!! 0%nat) = rbit_Z 64 x⌝ ∗
      P ∗
      True)
  )
)%I.
Global Instance : LithiumUnfold (rbit_spec) := I.

Lemma rbit stack_size :
  0 ≤ stack_size →
  instr 0x0 (Some a0) -∗
  instr 0x4 (Some a4) -∗
  instr_body 0x0 (rbit_spec stack_size).
Proof.
  move => ?. iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.

  rewrite !simplify_stuff. simpl.
  rewrite !bv_unsigned_BV. simpl.
  rewrite /rbit_Z /rbit_Z_aux /=.

  rewrite -(bv_wrap_wrap (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63)))).
  rewrite -(Z.shiftl_0_r (bv_wrap 64 (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63))))).
  repeat (rewrite simplify_more; [|lia|lia|lia]).

  repeat match goal with
  | |- Z.lor _ _ = _ => apply tac_lor_eq; last (evalZ; by destruct (Z.testbit _ _))
  | |- Z.land (Z.land _ _) _ = _ => rewrite -Z.land_assoc
  | |- Z.land _ _ = _ => rewrite Z.land_lor_distr_l
  end.

  vm_compute. by case_match.
Qed.

End proof.
