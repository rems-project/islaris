Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a60.

Lemma a60_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300060 (Some a60) -∗
  instr_body 0x10300060 (ldp_mapsto_spec 0x0000000010300060 "R20" "R19" "SP_EL2" (48) None).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a60_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 a60_spec.
Global Existing Instance a60_spec_inst.
