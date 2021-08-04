Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.instructions.stp.

Definition start_address := [BV{64} (0x0000000010300000 - 0x4)].
Definition spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300004] ].

Definition sys_regs `{!islaG Σ} `{!threadG} : iProp Σ :=
  ("SCTLR_EL2" ↦ᵣ Val_Bits [BV{64} 0x0000000004000002] ∗
  "SCR_EL3" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "TCR_EL2" ↦ᵣ Val_Bits [BV{64} 0] ∗
  "CFG_ID_AA64PFR0_EL1_EL0" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL1" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL2" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL3" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "OSLSR_EL1" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "OSDLR_EL1" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "EDSCR" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "MPIDR_EL1" ↦ᵣ Val_Bits [BV{64} 0] ∗
  "PSTATE" @ "SP" ↦ᵣ Val_Bits [BV{1} 1] ∗
  "PSTATE" @ "EL" ↦ᵣ Val_Bits [BV{2} 2] ∗
  "PSTATE" @ "nRW" ↦ᵣ Val_Bits [BV{1} 0] ∗
  "PSTATE" @ "D" ↦ᵣ Val_Bits [BV{1} 1]
)%I.

Definition cont_spec `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
  ∃ (vold1 vold2 : bv 64),
  "R0" ↦ᵣ Val_Bits v1 ∗
  "R1" ↦ᵣ Val_Bits v2 ∗
  (bv_sub sp [BV{64} 16]) ↦ₘ vold1 ∗
  (bv_sub sp [BV{64} 8]) ↦ₘ vold2 ∗
  ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  sys_regs ∗
  instr_pre a (
    "R0" ↦ᵣ Val_Bits v1 ∗
    "R1" ↦ᵣ Val_Bits v2 ∗
    "SP_EL2" ↦ᵣ Val_Bits (bv_sub sp [BV{64} 16])∗
    sys_regs ∗
    (bv_sub sp [BV{64} 16]) ↦ₘ v1 ∗
    (bv_sub sp [BV{64} 8]) ↦ₘ v2 ∗
    True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64):
  instr 0x0000000010300000 (Some [stp_trace]) -∗
  instr_body 0x0000000010300000 (cont_spec 0x0000000010300004 sp v1 v2).
Proof.
  iStartProof.
  unfold cont_spec, sys_regs.
  repeat liAStep; liShow.
  Unshelve.
  all: try (repeat f_equal; unLET; bv_solve).
Qed.
