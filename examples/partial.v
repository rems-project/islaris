Require Import isla.aarch64.aarch64.
From isla.instructions.partial Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Lemma partial_spec :
  instr 0x0000000010300000 (Some (partial_trace (Val_Bits (bv_0 16)) (partial_trace (Val_Bits (bv_0 2)) a7428))) -∗
  instr_body 0x0000000010300000 (
    ∃ (b : bv 64),
    "R0" ↦ᵣ RVal_Bits b ∗
    instr_pre 0x0000000010300004 (
      "R0" ↦ᵣ RVal_Bits b ∗
      True
  )).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  (* all: try bv_solve. *)
  - bv_simplify.
Abort.
