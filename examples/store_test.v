Require Import isla.isla.
Require Import isla.instructions.store.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
  [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] ∗
  "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
    [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000cafebabe] ∗
    "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
    reg_col sys_regs ∗
    True).

Lemma store_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some af9000029) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
