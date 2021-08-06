Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.instructions.store.

Definition start_address := [BV{64} (0x0000000010300000 - 0x4)].
Definition spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300004] ].

Lemma store_wp `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some [store_trace]) -∗
  instr 0x0000000010300004 None -∗
  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R1" ↦ᵣ Val_Bits [BV{64} 0x0000000000000008] -∗
  [BV{64} 0x0000000000000008] ↦ₘ [BV{64} 0x00000000deadbeef] -∗
  "R9" ↦ᵣ Val_Bits [BV{64} 0x00000000cafebabe] -∗
  "SCTLR_EL2" ↦ᵣ Val_Bits [BV{64} 0x0000000004000002] -∗
  "SCR_EL3" ↦ᵣ Val_Bits [BV{32} 0] -∗
  "TCR_EL2" ↦ᵣ Val_Bits [BV{64} 0] -∗
  "CFG_ID_AA64PFR0_EL1_EL0" ↦ᵣ Val_Bits [BV{1} 1] -∗
  "CFG_ID_AA64PFR0_EL1_EL1" ↦ᵣ Val_Bits [BV{1} 1] -∗
  "CFG_ID_AA64PFR0_EL1_EL2" ↦ᵣ Val_Bits [BV{1} 1] -∗
  "CFG_ID_AA64PFR0_EL1_EL3" ↦ᵣ Val_Bits [BV{1} 1] -∗
  "OSLSR_EL1" ↦ᵣ Val_Bits [BV{32} 0] -∗
  "OSDLR_EL1" ↦ᵣ Val_Bits [BV{32} 0] -∗
  "EDSCR" ↦ᵣ Val_Bits [BV{32} 0] -∗
  "MPIDR_EL1" ↦ᵣ Val_Bits [BV{64} 0] -∗
  "PSTATE" # "EL" ↦ᵣ Val_Bits [BV{2} 2] -∗
  "PSTATE" # "nRW" ↦ᵣ Val_Bits [BV{1} 0] -∗
  "PSTATE" # "D" ↦ᵣ Val_Bits [BV{1} 1] -∗
  spec_trace spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.
