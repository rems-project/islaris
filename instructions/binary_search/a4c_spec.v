Require Import isla.isla.
Require Export isla.instructions.binary_search.a4c.

Lemma a4c_spec `{!islaG Σ} `{!threadG}:
  instr 0x1030004c (Some a4c) -∗
  instr_body 0x1030004c (cmp_R_R_spec 0x000000001030004c "R20" "R23").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a4c_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a4c_spec.
Global Existing Instance a4c_spec_inst.
