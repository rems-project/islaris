Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a64.

Lemma a64_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a64)
  ⊢ instr_body pc (ldp_mapsto_spec pc "R22" "R21" "SP_EL2" (32) None).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a64_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a64_spec pc).
Global Existing Instance a64_spec_inst.
