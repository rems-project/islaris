Require Import isla.isla.
Require Export isla.instructions.binary_search.a44.

Lemma a44_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300044 (Some a44) -∗
  instr_body 0x10300044 (csel_spec 0x0000000010300044 "R20" "R24").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: csel_spec_tac.
Qed.

Definition a44_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a44_spec.
Global Existing Instance a44_spec_inst.
