Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a90.

Lemma a90_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a90) -∗
  instr_body pc (ld_spec pc "x8" "x2" (48)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a90_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a90_spec pc).
Global Existing Instance a90_spec_inst.
