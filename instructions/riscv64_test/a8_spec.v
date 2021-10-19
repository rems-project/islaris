Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.riscv64_test.a8.

Lemma a8_spec `{!islaG Σ} `{!threadG}:
  instr 0x10300008 (Some a8) -∗
  instr_body 0x10300008 (sd_spec 0x0000000010300008 "x11" "x2" (8)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a8_spec_inst `{!islaG Σ} `{!threadG} :=
  entails_to_simplify_hyp 0 a8_spec.
Global Existing Instance a8_spec_inst.
