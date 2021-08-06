Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.instructions.load.
Require Import isla.examples.sys_regs.

Definition spec `{!islaG Σ} `{!threadG} a : iProp Σ :=
  ∃ (vold : bv 64),
  "R1" ↦ᵣ Val_Bits [BV{64} 0x0000000000000008] ∗
  [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] ∗
  "R0" ↦ᵣ Val_Bits vold ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R1" ↦ᵣ Val_Bits [BV{64} 0x0000000000000008] ∗
    [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] ∗
    "R0" ↦ᵣ Val_Bits [BV{64} 0x00000000deadbeef] ∗
    reg_col sys_regs ∗
    True).

Lemma load_wp `{!islaG Σ} `{!threadG}:
  instr 0x0000000010300000 (Some [load_trace]) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
Qed.
