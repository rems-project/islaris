Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.riscv64_test.a8.

Lemma a8_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a8)
  ⊢ instr_body pc (sd_spec pc "x11" "x2" (8)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a8_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a8_spec pc).
Global Existing Instance a8_spec_inst.
