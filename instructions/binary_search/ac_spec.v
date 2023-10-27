Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.ac.

Lemma ac_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some ac)
  ⊢ instr_body pc (stp_uninit_spec pc "R20" "R19" "SP_EL2" (48) false).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition ac_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (ac_spec pc).
Global Existing Instance ac_spec_inst.
