Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7414.

Lemma a7414_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7414) -∗
  instr_body pc (ldp_mapsto_spec pc "R0" "R1" "SP_EL2" 0 None).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a7414_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7414_spec pc).
Global Existing Instance a7414_spec_inst.
