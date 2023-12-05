Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a1c.

Lemma a1c_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a1c)
  ⊢ instr_body pc (sd_spec pc "x21" "x2" (8)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a1c_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a1c_spec pc).
Global Existing Instance a1c_spec_inst.
