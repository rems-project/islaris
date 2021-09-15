Require Import isla.base.
Require Import isla.automation.

Definition sys_regs : list (reg_col_entry * valu) := [
  (RegColDirect "SCTLR_EL2" , RegVal_Base (Val_Bits [BV{64} 0x0000000004000002]) );
  (RegColDirect "SCR_EL3" , RegVal_Base (Val_Bits [BV{32} 0]) );
  (RegColDirect "TCR_EL2" , RegVal_Base (Val_Bits [BV{64} 0]) );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL0" , RegVal_Base (Val_Bits [BV{4} 1]) );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL1" , RegVal_Base (Val_Bits [BV{4} 1]) );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL2" , RegVal_Base (Val_Bits [BV{4} 1]) );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL3" , RegVal_Base (Val_Bits [BV{4} 1]) );
  (RegColDirect "OSLSR_EL1" , RegVal_Base (Val_Bits [BV{32} 0]) );
  (RegColDirect "OSDLR_EL1" , RegVal_Base (Val_Bits [BV{32} 0]) );
  (RegColDirect "EDSCR" , RegVal_Base (Val_Bits [BV{32} 0]) );
  (RegColDirect "MPIDR_EL1" , RegVal_Base (Val_Bits [BV{64} 0]) );
  (RegColStruct "PSTATE" "SP" , RegVal_Base (Val_Bits [BV{1} 1]) );
  (RegColStruct "PSTATE" "EL" , RegVal_Base (Val_Bits [BV{2} 2]) );
  (RegColStruct "PSTATE" "nRW" , RegVal_Base (Val_Bits [BV{1} 0]) );
  (RegColStruct "PSTATE" "D" , RegVal_Base (Val_Bits [BV{1} 1]))
].

Definition sys_regs_map : reg_map :=
  <[ "SCTLR_EL2" := Val_Bits [BV{64} 0x0000000004000002] ]> $
  <[ "SCR_EL3" := Val_Bits [BV{32} 0] ]> $
  <[ "TCR_EL2" := Val_Bits [BV{64} 0] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL0" := Val_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL1" := Val_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL2" := Val_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL3" := Val_Bits [BV{4} 1] ]> $
  <[ "OSLSR_EL1" := Val_Bits [BV{32} 0] ]> $
  <[ "OSDLR_EL1" := Val_Bits [BV{32} 0] ]> $
  <[ "EDSCR" := Val_Bits [BV{32} 0] ]> $
  <[ "MPIDR_EL1" := Val_Bits [BV{64} 0] ]> $
  <[ "PSTATE" := (Val_Struct
    [("GE", Val_Poison); ("F", Val_Poison);
    ("UAO", Val_Poison); ("C", Val_Bits [BV{1} 0]);
    ("SP", Val_Bits [BV{1} 1]); ("N", Val_Bits [BV{1} 0]);
    ("Q", Val_Poison); ("A", Val_Poison); ("SS", Val_Poison);
    ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Poison);
    ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits [BV{1} 1]);
    ("nRW", Val_Bits [BV{1} 0]); ("EL", Val_Bits [BV{2} 2]);
    ("IT", Val_Poison); ("IL", Val_Poison);
    ("Z", Val_Bits [BV{1} 0]); ("BTYPE", Val_Poison);
    ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
    ("V", Val_Bits [BV{1} 0]); ("DIT", Val_Poison)]) ]> $ ∅.

Section sys_regs.
  Context `{!islaG Σ} `{!threadG}.

  Lemma sys_regs_init regs:
    regs_ctx regs -∗
    ([∗ map] k↦y ∈ sys_regs_map, k ↦ᵣ y) ==∗
    regs_ctx regs ∗
    reg_col sys_regs ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits [BV{1} 0] ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits [BV{1} 0] ∗
    "PSTATE" # "V" ↦ᵣ Val_Bits [BV{1} 0] ∗
    "PSTATE" # "Z" ↦ᵣ Val_Bits [BV{1} 0].
  Proof.
    rewrite /reg_col/=.
    repeat (rewrite big_sepM_insert;[ | by vm_compute]).
    iIntros "Hctx H". repeat iDestruct "H" as "[$ H]".
    iDestruct "H" as "[HPSTATE _]".
    iMod (reg_mapsto_to_struct_reg_mapsto with "Hctx HPSTATE") as "[$ H]".
    { simpl. repeat (constructor; [set_solver|]). constructor. }
    simpl. repeat (iDestruct "H" as "[Hf H]"; first [ iFrame "Hf" | iClear "Hf"]).
    done.
  Qed.
End sys_regs.

Global Opaque sys_regs_map.
