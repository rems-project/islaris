Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7430.

Lemma a7430_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7430) -∗
  instr_body pc (movk_spec pc "R6" 0 0).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  by bits_simplify.
Qed.

Definition a7430_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7430_spec pc).
Global Existing Instance a7430_spec_inst.
