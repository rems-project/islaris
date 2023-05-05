Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7438.

Lemma a7438_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7438)
  ⊢ instr_body pc (sub_R_R_R_self_spec pc "R5" "R6").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all:bv_solve.
Qed.

Definition a7438_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7438_spec pc).
Global Existing Instance a7438_spec_inst.
