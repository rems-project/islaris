Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a2c.

Lemma a2c_spec `{!islaG Σ} `{!threadG}:
  instr 0x1030002c (Some a2c) -∗
  instr_body 0x1030002c (sub_R_R_R_spec 0x000000001030002c "R8" "R20" "R23").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a2c_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a2c_spec.
Global Existing Instance a2c_spec_inst.
