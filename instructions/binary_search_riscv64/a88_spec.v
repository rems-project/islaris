Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a88.

Lemma a88_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a88) -∗
  instr_body pc (ld_spec pc "x18" "x2" (32)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a88_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a88_spec pc).
Global Existing Instance a88_spec_inst.
