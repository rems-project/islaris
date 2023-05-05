Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7408.

Lemma a7408_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7408) ⊢
  instr_body pc (lsr_R_spec pc "R0" 26).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  by bv_simplify; bitblast.
Qed.

Definition a7408_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7408_spec pc).
Global Existing Instance a7408_spec_inst.
