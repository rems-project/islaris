Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a8.

Lemma a8_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a8) -∗
  instr_body pc (stp_uninit_spec pc "R22" "R21" "SP_EL2" (32) false).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a8_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a8_spec pc).
Global Existing Instance a8_spec_inst.
