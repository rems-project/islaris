Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a68.

Lemma a68_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300068 (Some a68) -∗
  instr_body 0x10300068 (ldp_mapsto_spec 0x0000000010300068 "R24" "R23" "SP_EL2" (16) None).
Proof.
Admitted.

Definition a68_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 a68_spec.
Global Existing Instance a68_spec_inst.
