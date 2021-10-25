Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a0.

Lemma a0_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a0) -∗
  instr_body pc (stp_uninit_spec pc "R29" "R30" "SP_EL2" (-64) true).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a0_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a0_spec pc).
Global Existing Instance a0_spec_inst.
