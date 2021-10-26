Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a742c.

Lemma a742c_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a742c) -∗
  instr_body pc (movk_spec pc "R6" 0 0).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  by bits_simplify.
Qed.

Definition a742c_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a742c_spec pc).
Global Existing Instance a742c_spec_inst.
