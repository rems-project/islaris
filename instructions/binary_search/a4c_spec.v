Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a4c.

Lemma a4c_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a4c) -∗
  instr_body pc (cmp_R_R_spec pc "R20" "R23").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a4c_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a4c_spec pc).
Global Existing Instance a4c_spec_inst.
