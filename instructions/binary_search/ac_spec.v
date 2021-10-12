Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.ac.

Lemma ac_spec `{!islaG Σ} `{!threadG}:
  instr 0x1030000c (Some ac) -∗
  instr_body 0x1030000c (stp_uninit_spec 0x000000001030000c "R20" "R19" "SP_EL2" (48) false).
Proof.
Admitted.

Definition ac_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 ac_spec.
Global Existing Instance ac_spec_inst.
