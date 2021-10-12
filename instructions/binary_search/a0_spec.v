Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a0.

Lemma a0_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300000 (Some a0) -∗
  instr_body 0x10300000 (stp_uninit_spec 0x0000000010300000 "R29" "R30" "SP_EL2" (-64) true).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a0_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a0_spec.
Global Existing Instance a0_spec_inst.
