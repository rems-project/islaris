Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.riscv64_test.ac.

Lemma ac_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some ac) -∗
  instr_body pc (ld_spec pc "x11" "x2" (8)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition ac_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (ac_spec pc).
Global Existing Instance ac_spec_inst.
