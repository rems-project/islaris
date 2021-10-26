Require Import isla.isla.
Require Import isla.aarch64.aarch64.
Require Export isla.examples.pkvm_handler.a7424.

Lemma a7424_spec `{!islaG Σ} `{!threadG} pc:
  instr pc (Some a7424) -∗
  instr_body pc (ldr_mapsto_spec pc 0x7424 "R5" [BV{64} 0x77f8]).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
Qed.

Definition a7424_spec_inst `{!islaG Σ} `{!threadG} pc :=
  entails_to_simplify_hyp 0 (a7424_spec pc).
Global Existing Instance a7424_spec_inst.
