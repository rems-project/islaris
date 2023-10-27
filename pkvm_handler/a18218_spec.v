Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a18218.

Lemma a18218_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a18218)
  ⊢ instr_body pc (cmp_R_imm_spec pc "R0" 0x1).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a18218_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a18218_spec pc).
Global Existing Instance a18218_spec_inst.
