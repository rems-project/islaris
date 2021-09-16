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
  <[ "SCTLR_EL2" := RegVal_Base (Val_Bits [BV{64} 0x0000000004000002]) ]> $
  <[ "SCR_EL3" := RegVal_Base (Val_Bits [BV{32} 0]) ]> $
  <[ "TCR_EL2" := RegVal_Base (Val_Bits [BV{64} 0]) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL0" := RegVal_Base (Val_Bits [BV{4} 1]) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL1" := RegVal_Base (Val_Bits [BV{4} 1]) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL2" := RegVal_Base (Val_Bits [BV{4} 1]) ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL3" := RegVal_Base (Val_Bits [BV{4} 1]) ]> $
  <[ "OSLSR_EL1" := RegVal_Base (Val_Bits [BV{32} 0]) ]> $
  <[ "OSDLR_EL1" := RegVal_Base (Val_Bits [BV{32} 0]) ]> $
  <[ "EDSCR" := RegVal_Base (Val_Bits [BV{32} 0]) ]> $
  <[ "MPIDR_EL1" := RegVal_Base (Val_Bits [BV{64} 0]) ]> $
  <[ "PSTATE" := (RegVal_Struct
    [("GE", RegVal_Poison); ("F", RegVal_Poison);
    ("UAO", RegVal_Poison); ("C", RegVal_Base (Val_Bits [BV{1} 0]));
    ("SP", RegVal_Base (Val_Bits [BV{1} 1])); ("N", RegVal_Base (Val_Bits [BV{1} 0]));
    ("Q", RegVal_Poison); ("A", RegVal_Poison); ("SS", RegVal_Poison);
    ("E", RegVal_Poison); ("TCO", RegVal_Poison); ("I", RegVal_Poison);
    ("PAN", RegVal_Poison); ("M", RegVal_Poison); ("D", RegVal_Base (Val_Bits [BV{1} 1]));
    ("nRW", RegVal_Base (Val_Bits [BV{1} 0])); ("EL", RegVal_Base (Val_Bits [BV{2} 2]));
    ("IT", RegVal_Poison); ("IL", RegVal_Poison);
    ("Z", RegVal_Base (Val_Bits [BV{1} 0])); ("BTYPE", RegVal_Poison);
    ("SSBS", RegVal_Poison); ("T", RegVal_Poison); ("J", RegVal_Poison);
    ("V", RegVal_Base (Val_Bits [BV{1} 0])); ("DIT", RegVal_Poison)]) ]> $ ∅.

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
