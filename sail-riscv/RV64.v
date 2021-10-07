Require Import refinedc.lithium.base.
Require Export Sail.Base.
Require Export Sail.Prompt_monad.
Require Export RV64.riscv_types.
Require Export RV64.mem_metadata.
Require Export RV64.riscv_extras.
Require Export RV64.riscv.

(* This file should not depend on anything in isla-coq since it is quite slow to compile. *)

Lemma get_word_word_binop {n} f (b1 b2 : mword n):
  get_word (word_binop f b1 b2) = f _ (get_word b1) (get_word b2).
Proof. by destruct n. Qed.

Lemma get_set_regval r regs regs' v:
  set_regval r v regs = Some regs' ->
  get_regval r regs' = Some v.
Proof.
  unfold set_regval, get_regval.
  have Hcase : ∀ s e1 e2 e1' e2',
      (r = s → e1 = Some regs' → e1' = Some v) →
      (e2 = Some regs' → e2' = Some v) →
      (if string_dec r s then e1 else e2) = Some regs' →
      (if string_dec r s then e1' else e2') = Some v. {
    move => s ??????. destruct (string_dec r s); eauto.
  }
  Time repeat (apply Hcase; [shelve|]). done.
  Unshelve.
  Time all: clear Hcase; move => ?; simpl; destruct v => //= ?; simplify_eq; try by destruct regs.
Admitted.


Lemma get_set_regval_ne r r' regs regs' v:
  set_regval r' v regs = Some regs' →
  r ≠ r' →
  get_regval r regs' = get_regval r regs.
Proof.
  unfold set_regval, get_regval.
  move => Hset Hneq.
  have Hcase : ∀ s (e1 e2 e1' e2' : option register_value),
      (r = s → e1 = e1') →
      (e2 = e2') →
      (if string_dec r s then e1 else e2) = (if string_dec r s then e1' else e2'). {
    move => s ??????. destruct (string_dec r s); eauto.
  }
  have Hcase2 : ∀ s e1 e2 (P : Prop),
      (r' = s → e1 = Some regs' → P) →
      (e2 = Some regs' → P) →
      (if string_dec r' s then e1 else e2) = Some regs' →
      P. {
    move => s ??????. destruct (string_dec r' s); eauto.
  }
  repeat (apply Hcase; [shelve|]). done.
  Unshelve.
  (* all: clear Hcase; move => ?; subst r; simpl; move: Hset; repeat (apply Hcase2; [shelve|]); done. *)
Admitted.
