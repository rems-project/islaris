Require Import isla.isla.
Require Export isla.instructions.binary_search.a64.

Lemma a64_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300064 (Some a64) -∗
  instr_body 0x10300064 (ldp_mapsto_spec 0x0000000010300064 "R22" "R21" "SP_EL2" (32) None).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a64_spec_inst `{!islaG Σ} `{!threadG} := entails_to_simplify_hyp 0 a64_spec.
Global Existing Instance a64_spec_inst.
