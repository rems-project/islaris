Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a94.

Lemma a94_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a94) ⊢
  instr_body pc (ld_spec pc "x1" "x2" (56)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a94_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a94_spec pc).
Global Existing Instance a94_spec_inst.
