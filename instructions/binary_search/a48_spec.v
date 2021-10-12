Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a48.

Lemma a48_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300048 (Some a48) -∗
  instr_body 0x10300048 (csinc_spec 0x0000000010300048 "R23" "R24").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: csinc_spec_tac.
Qed.

Definition a48_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a48_spec.
Global Existing Instance a48_spec_inst.
