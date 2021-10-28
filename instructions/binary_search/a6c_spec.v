Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a6c.

Lemma a6c_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a6c) -∗
  instr_body pc (ldp_mapsto_spec pc "R29" "R30" "SP_EL2" (0) (Some 64)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a6c_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a6c_spec pc).
Global Existing Instance a6c_spec_inst.
