Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a8c.

Lemma a8c_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a8c) ⊢
  instr_body pc (ld_spec pc "x9" "x2" (40)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a8c_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a8c_spec pc).
Global Existing Instance a8c_spec_inst.
