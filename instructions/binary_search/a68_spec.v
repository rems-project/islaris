Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.instructions.binary_search.a68.

Lemma a68_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a68) ⊢
  instr_body pc (ldp_mapsto_spec pc "R24" "R23" "SP_EL2" (16) None).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a68_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a68_spec pc).
Global Existing Instance a68_spec_inst.
