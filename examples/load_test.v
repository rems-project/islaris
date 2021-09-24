Require Import isla.isla.
Require Import isla.instructions.load.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  ∃ (vold : bv 64),
  "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
  [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] ∗
  "R0" ↦ᵣ RVal_Bits vold ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
    [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] ∗
    "R0" ↦ᵣ RVal_Bits [BV{64} 0x00000000deadbeef] ∗
    reg_col sys_regs ∗
    True).

Lemma load_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some af9400020) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
