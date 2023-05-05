Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a74.

Lemma a74_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a74) ⊢
  instr_body pc (cmp_R_R_spec pc "R0" "R1").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a74_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a74_spec pc).
Global Existing Instance a74_spec_inst.
