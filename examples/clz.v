Require Import isla.aarch64.aarch64.
From isla.instructions.clz Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Axiom clz_Z : Z → Z.

Definition clz_spec (stack_size : Z) : iProp Σ := (
  c_call stack_size (λ args sp RET,
    ∃ (x : Z) P,
    ⌜bv_unsigned (args !!! 0%nat) = x⌝ ∗
    P ∗
    RET (λ rets,
      ⌜bv_unsigned (rets !!! 0%nat) = clz_Z x⌝ ∗
      P ∗
      True)
  )
)%I.
Global Instance : LithiumUnfold (clz_spec) := I.

Lemma clz stack_size :
  0 ≤ stack_size →
  instr 0x0 (Some a0) -∗
  instr 0x4 (Some a4) -∗
  instr_body 0x0 (clz_spec stack_size).
Proof.
  move => ?. iStartProof.
  (* do 100 liAStep; liShow. *)
  (* do 100 liAStep; liShow. *)
  (* do 100 liAStep; liShow. *)
Admitted.

End proof.
