Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export isla.instructions.binary_search_riscv64.a10.

Lemma a10_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a10)
  ⊢ instr_body pc (sd_spec pc "x18" "x2" (32)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition a10_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a10_spec pc).
Global Existing Instance a10_spec_inst.
