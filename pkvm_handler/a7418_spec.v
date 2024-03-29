Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7418.

Lemma a7418_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7418)
  ⊢ instr_body pc (cmp_R_imm_spec pc "R0" 0x3).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  1: cmp_spec_tac1. 1: cmp_spec_tac2. 1: cmp_spec_tac3. 1: cmp_spec_tac4.
Qed.

Definition a7418_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7418_spec pc).
Global Existing Instance a7418_spec_inst.
