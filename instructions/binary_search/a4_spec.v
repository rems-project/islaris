Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a4.

Lemma a4_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a4) -∗
  instr_body pc (stp_uninit_spec pc "R24" "R23" "SP_EL2" (16) false).
Proof.
Admitted.

Definition a4_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a4_spec pc).
Global Existing Instance a4_spec_inst.
