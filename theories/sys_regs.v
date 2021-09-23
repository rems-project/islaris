Require Import isla.base.
Require Import isla.automation.

Definition sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "SCTLR_EL2" , ExactShape (RVal_Bits [BV{64} 0x0000000004000002] ));
  (KindReg "SCR_EL3" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "TCR_EL2" , ExactShape (RVal_Bits [BV{64} 0] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL0" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL1" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL2" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL3" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "OSLSR_EL1" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "OSDLR_EL1" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "EDSCR" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "MPIDR_EL1" , ExactShape (RVal_Bits [BV{64} 0] ));
  (KindField "PSTATE" "SP" , ExactShape (RVal_Bits [BV{1} 1] ));
  (KindField "PSTATE" "EL" , ExactShape (RVal_Bits [BV{2} 2] ));
  (KindField "PSTATE" "nRW" , ExactShape (RVal_Bits [BV{1} 0] ));
  (KindField "PSTATE" "D" , ExactShape (RVal_Bits [BV{1} 1]))
].

Definition CNVZ_regs : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "C", BitsShape 1);
  (KindField "PSTATE" "N", BitsShape 1);
  (KindField "PSTATE" "V", BitsShape 1);
  (KindField "PSTATE" "Z", BitsShape 1)
].

Definition sys_regs_map : reg_map :=
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
     ("V", RVal_Bits [BV{1} 0]); ("DIT", RegVal_Poison)]) ]> $
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
  <[ "MPIDR_EL1" := RVal_Bits [BV{64} 0] ]> $ ∅.

Section sys_regs.
  Context `{!islaG Σ} `{!threadG}.

  Lemma sys_regs_init regs:
    regs_ctx regs -∗
    ([∗ map] k↦y ∈ sys_regs_map, k ↦ᵣ y) ==∗
    regs_ctx regs ∗
    reg_col sys_regs ∗
    reg_col CNVZ_regs.
  Proof.
    repeat (rewrite big_sepM_insert;[ | by vm_compute]).
    iIntros "Hctx [HPSTATE H]".
    iMod (reg_mapsto_to_struct_reg_mapsto with "Hctx HPSTATE") as "[$ HPSTATE]".
    { simpl. repeat (constructor; [set_solver|]). constructor. }
    simpl. iModIntro. rewrite -(right_id True%I _ (reg_col CNVZ_regs)).
    iRevert "H HPSTATE". repeat liAStep; liShow.
  Qed.
End sys_regs.

Global Opaque sys_regs_map.
