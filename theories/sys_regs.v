Require Import isla.base.
Require Import isla.automation.

Definition sys_regs : list (reg_col_entry * option valu) := [
  (RegColDirect "SCTLR_EL2" , Some (RVal_Bits [BV{64} 0x0000000004000002] ));
  (RegColDirect "SCR_EL3" , Some (RVal_Bits [BV{32} 0] ));
  (RegColDirect "TCR_EL2" , Some (RVal_Bits [BV{64} 0] ));
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL0" , Some (RVal_Bits [BV{4} 1] ));
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL1" , Some (RVal_Bits [BV{4} 1] ));
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL2" , Some (RVal_Bits [BV{4} 1] ));
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL3" , Some (RVal_Bits [BV{4} 1] ));
  (RegColDirect "OSLSR_EL1" , Some (RVal_Bits [BV{32} 0] ));
  (RegColDirect "OSDLR_EL1" , Some (RVal_Bits [BV{32} 0] ));
  (RegColDirect "EDSCR" , Some (RVal_Bits [BV{32} 0] ));
  (RegColDirect "MPIDR_EL1" , Some (RVal_Bits [BV{64} 0] ));
  (RegColStruct "PSTATE" "SP" , Some (RVal_Bits [BV{1} 1] ));
  (RegColStruct "PSTATE" "EL" , Some (RVal_Bits [BV{2} 2] ));
  (RegColStruct "PSTATE" "nRW" , Some (RVal_Bits [BV{1} 0] ));
  (RegColStruct "PSTATE" "D" , Some (RVal_Bits [BV{1} 1]))
].

Definition CNVZ_regs : list (reg_col_entry * option valu) := [
  (RegColStruct "PSTATE" "C", None);
  (RegColStruct "PSTATE" "N", None);
  (RegColStruct "PSTATE" "V", None);
  (RegColStruct "PSTATE" "Z", None)
].

Definition sys_regs_map : reg_map :=
  <[ "SCTLR_EL2" := RVal_Bits [BV{64} 0x0000000004000002] ]> $
  <[ "SCR_EL3" := RVal_Bits [BV{32} 0] ]> $
  <[ "TCR_EL2" := RVal_Bits [BV{64} 0] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL0" := RVal_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL1" := RVal_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL2" := RVal_Bits [BV{4} 1] ]> $
  <[ "CFG_ID_AA64PFR0_EL1_EL3" := RVal_Bits [BV{4} 1] ]> $
  <[ "OSLSR_EL1" := RVal_Bits [BV{32} 0] ]> $
  <[ "OSDLR_EL1" := RVal_Bits [BV{32} 0] ]> $
  <[ "EDSCR" := RVal_Bits [BV{32} 0] ]> $
  <[ "MPIDR_EL1" := RVal_Bits [BV{64} 0] ]> $
  <[ "PSTATE" := (RegVal_Struct
    [("GE", RegVal_Poison); ("F", RegVal_Poison);
    ("UAO", RegVal_Poison); ("C", RVal_Bits [BV{1} 0]);
    ("SP", RVal_Bits [BV{1} 1]); ("N", RVal_Bits [BV{1} 0]);
    ("Q", RegVal_Poison); ("A", RegVal_Poison); ("SS", RegVal_Poison);
    ("E", RegVal_Poison); ("TCO", RegVal_Poison); ("I", RegVal_Poison);
    ("PAN", RegVal_Poison); ("M", RegVal_Poison); ("D", RVal_Bits [BV{1} 1]);
    ("nRW", RVal_Bits [BV{1} 0]); ("EL", RVal_Bits [BV{2} 2]);
    ("IT", RegVal_Poison); ("IL", RegVal_Poison);
    ("Z", RVal_Bits [BV{1} 0]); ("BTYPE", RegVal_Poison);
    ("SSBS", RegVal_Poison); ("T", RegVal_Poison); ("J", RegVal_Poison);
    ("V", RVal_Bits [BV{1} 0]); ("DIT", RegVal_Poison)]) ]> $ ∅.

Section sys_regs.
  Context `{!islaG Σ} `{!threadG}.

  Lemma sys_regs_init regs:
    regs_ctx regs -∗
    ([∗ map] k↦y ∈ sys_regs_map, k ↦ᵣ y) ==∗
    regs_ctx regs ∗
    reg_col sys_regs ∗
    reg_col CNVZ_regs.
  Proof.
    rewrite !reg_col_cons_Some !reg_col_cons_None reg_col_nil.
    repeat (rewrite big_sepM_insert;[ | by vm_compute]).
    iIntros "Hctx H". repeat iDestruct "H" as "[$ H]".
    iDestruct "H" as "[HPSTATE _]".
    iMod (reg_mapsto_to_struct_reg_mapsto with "Hctx HPSTATE") as "[$ H]".
    { simpl. repeat (constructor; [set_solver|]). constructor. }
    simpl. iModIntro. iRevert "H".
    repeat liAStep; liShow.
  Qed.
End sys_regs.

Global Opaque sys_regs_map.
