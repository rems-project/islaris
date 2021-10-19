Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.riscv64_test.ac.

Lemma ac_spec `{!islaG Σ} `{!threadG}:
  instr 0x1030000c (Some ac) -∗
  instr_body 0x1030000c (ld_spec 0x000000001030000c "x11" "x2" (8)).
Proof.
  iStartProof.
  repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition ac_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 ac_spec.
Global Existing Instance ac_spec_inst.
