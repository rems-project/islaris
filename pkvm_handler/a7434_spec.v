Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7434.

Lemma a7434_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7434) -∗
  instr_body pc (movk_spec pc "R6" 0 0).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  by bits_simplify.
Qed.

Definition a7434_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7434_spec pc).
Global Existing Instance a7434_spec_inst.
