Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a74.

Lemma a74_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300074 (Some a74) -∗
  instr_body 0x10300074 (cmp_R_R_spec 0x0000000010300074 "R0" "R1").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a74_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 a74_spec.
Global Existing Instance a74_spec_inst.
