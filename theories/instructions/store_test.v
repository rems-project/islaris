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
  "PSTATE" ↦ᵣ (Val_Struct
          [("GE", Val_Poison); ("F", Val_Bits [BV{1} 1]);
          ("UAO", Val_Poison); ("C", Val_Bits [BV{1} 0]);
          ("SP", Val_Poison); ("N", Val_Bits [BV{1} 0]);
          ("Q", Val_Poison); ("A", Val_Bits [BV{1} 1]); ("SS", Val_Bits [BV{1} 0]);
          ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Bits [BV{1} 1]);
          ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits [BV{1} 1]);
          ("nRW", Val_Bits [BV{1} 0]); ("EL", Val_Bits [BV{2} 2]);
          ("IT", Val_Poison); ("IL", Val_Bits [BV{1} 0]);
          ("Z", Val_Bits [BV{1} 0]); ("BTYPE", Val_Poison);
          ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
          ("V", Val_Bits [BV{1} 0]); ("DIT", Val_Bits [BV{1} 0])]) -∗
  spec_trace spec -∗
  WPasm [].
Proof.
    iStartProof.
    repeat liAStep; liShow.
Qed.
