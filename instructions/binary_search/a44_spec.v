Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a44.

Lemma a44_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a44) -∗
  instr_body pc (csel_spec pc "R20" "R24").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: csel_spec_tac.
Qed.

Definition a44_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a44_spec pc).
Global Existing Instance a44_spec_inst.
