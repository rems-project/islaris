Require Import isla.isla.
Require Export isla.instructions.binary_search.a8.

Lemma a8_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300008 (Some a8) -∗
  instr_body 0x10300008 (stp_uninit_spec 0x0000000010300008 "R22" "R21" "SP_EL2" (32) false).
Proof.
Admitted.

Definition a8_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a8_spec.
Global Existing Instance a8_spec_inst.
