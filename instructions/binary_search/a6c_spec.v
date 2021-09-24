Require Import isla.isla.
Require Export isla.instructions.binary_search.a6c.

Lemma a6c_spec `{!islaG Σ} `{!threadG}:
  instr 0x1030006c (Some a6c) -∗
  instr_body 0x1030006c (ldp_mapsto_spec 0x000000001030006c "R29" "R30" "SP_EL2" (0) (Some 64)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a6c_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a6c_spec.
Global Existing Instance a6c_spec_inst.
