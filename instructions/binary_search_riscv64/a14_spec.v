Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a14.

Lemma a14_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a14)
  ⊢ instr_body pc (sd_spec pc "x19" "x2" (24)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a14_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a14_spec pc).
Global Existing Instance a14_spec_inst.
