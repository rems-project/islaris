Require Import isla.aarch64.aarch64.
Require Import isla.instructions.instr_str.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
  0x0000000000000008 ↦ₘ [BV{64} 0x00000000deadbeef] ∗
  "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R1" ↦ᵣ RVal_Bits [BV{64} 0x0000000000000008] ∗
    0x0000000000000008 ↦ₘ [BV{64} 0x00000000cafebabe] ∗
    "R9" ↦ᵣ RVal_Bits [BV{64} 0x00000000cafebabe] ∗
    reg_col sys_regs ∗
    True).

Lemma store_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some instr_str) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
