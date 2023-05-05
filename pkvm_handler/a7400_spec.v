Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7400.

Lemma a7400_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7400) ⊢
  instr_body pc (stp_uninit_spec pc "R0" "R1" "SP_EL2" (-16) true).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a7400_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7400_spec pc).
Global Existing Instance a7400_spec_inst.
