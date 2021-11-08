Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a80.

Lemma a80_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a80) -∗
  instr_body pc (ld_spec pc "x20" "x2" (16)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a80_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a80_spec pc).
Global Existing Instance a80_spec_inst.
