Require Import isla.aarch64.aarch64.
From isla.instructions.rbit Require Import instrs.

(*PROOF_START*)
Lemma simplify_stuff (b n : bv 64) :
  bv_extract 0 1 (bv_shiftr b n) = bool_to_bv 1 (Z.testbit (bv_unsigned b) (bv_unsigned n)).
Proof.
  bv_simplify. rewrite /bv_wrap.
  assert (bv_modulus 1 = 2) as -> by done.
  generalize (bv_unsigned b) (bv_unsigned n) => bz nz; clear b n.
  assert (∀ b, bool_to_Z b `mod` 2 = bool_to_Z b) as -> by move => [] //.
  rewrite -(Z.land_ones _ 1); last done.
  bitblast; rewrite /= ?Z.testbit_0_l //.
  - assert (i = 0) as -> by lia. by rewrite Z_of_bool_spec_low.
  - symmetry. apply Z_of_bool_spec_high. lia.
Qed.

Lemma simplify_more {N} (b : bv N) (n k : Z):
  0 ≤ n →
  0 ≤ k →
  k + n = Z.of_N N - 1 →
  bv_wrap N (bv_wrap N (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b) k))) ≪ n) =
  bool_to_Z (Z.testbit (bv_unsigned b) k) ≪ n.
Proof.
  move => ?? HN. rewrite /bv_wrap. generalize (bv_unsigned b) => z. clear b.
  rewrite /bv_modulus. assert (2 ^ Z.of_N 1 = 2) as -> by lia.
  assert (0 ≤ Z.of_N N) as HN0 by lia. revert HN0 HN. generalize (Z.of_N N) => Z. clear N.
  move => ??. bitblast.
  all: rewrite ?Zmod_0_l ?Z.shiftl_0_l ?Zmod_0_l ?Z.testbit_0_l //.
  - rewrite Z.testbit_mod_pow2; last lia.
    rewrite Z.shiftl_spec; last lia.
    rewrite Z.testbit_mod_pow2; last lia.
    assert (Z.testbit _ (i - n) = false) as ->; last by rewrite !andb_false_r.
    destruct (Z.testbit z k) => /=; last by rewrite Z.testbit_0_l.
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
(*PROOF_END*)

(*SPEC_START*)
Fixpoint rbit_Z_aux (N : nat) (z : Z) (n : nat) : Z :=
  match n with
  | O   => 0
  | S n => Z.lor (rbit_Z_aux N z n) ((bool_to_Z (Z.testbit z n)) ≪ (N - S n)%nat)
  end.

Definition rbit_Z N z := rbit_Z_aux N z N.
(*SPEC_END*)

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*SPEC_START*)
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
(*SPEC_END*)
Global Instance : LithiumUnfold (rbit_spec) := I.

Lemma rbit stack_size :
(*SPEC_START*)
  0 ≤ stack_size →
(*SPEC_END*)
  instr 0x0 (Some a0) -∗
  instr 0x4 (Some a4) -∗
  instr_body 0x0 (rbit_spec stack_size).
Proof.
(*PROOF_START*)
  move => ?. iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.

  rewrite !simplify_stuff. simpl.
  rewrite !bv_unsigned_BV. simpl.
  rewrite /rbit_Z /rbit_Z_aux /=.

  rewrite -(bv_wrap_idemp _ (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63)))).
  rewrite -(Z.shiftl_0_r (bv_wrap 64 (bv_wrap 1 (bool_to_Z (Z.testbit (bv_unsigned b0) 63))))).
  repeat (rewrite simplify_more; [|lia|lia|lia]).
  rewrite /Z.of_nat /=.

  repeat match goal with
  | |- Z.lor _ _ = Z.lor _ _ => f_equal
  | |- Z.land (Z.land _ _) _ = _ => rewrite -Z.land_assoc
  | |- Z.land _ _ = _ => rewrite Z.land_lor_distr_l
  | |- _ = bool_to_Z _ ≪ _ => by destruct (Z.testbit _ _)
  end.

  vm_compute. by case_match.
(*PROOF_END*)
Time Qed.

End proof.
