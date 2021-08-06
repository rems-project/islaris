Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.instructions.stp.
Require Import isla.examples.sys_regs.

Definition spec `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
  ∃ (vold1 vold2 : bv 64),
  "R0" ↦ᵣ Val_Bits v1 ∗
  "R1" ↦ᵣ Val_Bits v2 ∗
  (bv_sub sp [BV{64} 16]) ↦ₘ vold1 ∗
  (bv_sub sp [BV{64} 8]) ↦ₘ vold2 ∗
  ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  reg_col sys_regs ∗
  instr_pre a (
    "R0" ↦ᵣ Val_Bits v1 ∗
    "R1" ↦ᵣ Val_Bits v2 ∗
    "SP_EL2" ↦ᵣ Val_Bits (bv_sub sp [BV{64} 16])∗
    reg_col sys_regs ∗
    (bv_sub sp [BV{64} 16]) ↦ₘ v1 ∗
    (bv_sub sp [BV{64} 8]) ↦ₘ v2 ∗
    True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64):
  instr 0x0000000010300000 (Some [stp_trace]) -∗
  instr_body 0x0000000010300000 (spec 0x0000000010300004 sp v1 v2).
Proof.
  iStartProof.
  unfold spec.
  repeat liAStep; liShow.
  Unshelve.
  all: try (repeat f_equal; bv_solve).
Qed.
