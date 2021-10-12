Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a4.

Lemma a4_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300004 (Some a4) -∗
  instr_body 0x10300004 (stp_uninit_spec 0x0000000010300004 "R24" "R23" "SP_EL2" (16) false).
Proof.
Admitted.

Definition a4_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a4_spec.
Global Existing Instance a4_spec_inst.
