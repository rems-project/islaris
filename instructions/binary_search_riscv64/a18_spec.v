Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a18.

Lemma a18_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a18)
  ⊢ instr_body pc (sd_spec pc "x20" "x2" (16)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a18_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a18_spec pc).
Global Existing Instance a18_spec_inst.
