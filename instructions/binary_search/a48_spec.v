Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a48.

Lemma a48_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a48)
  ⊢ instr_body pc (csinc_spec pc "R23" "R24").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: csinc_spec_tac.
Qed.

Definition a48_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a48_spec pc).
Global Existing Instance a48_spec_inst.
