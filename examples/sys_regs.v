Require Import isla.base.
Require Import isla.automation.

Definition sys_regs : list (reg_col_entry * valu) := [
  (RegColDirect "SCTLR_EL2" , Val_Bits [BV{64} 0x0000000004000002] );
  (RegColDirect "SCR_EL3" , Val_Bits [BV{32} 0] );
  (RegColDirect "TCR_EL2" , Val_Bits [BV{64} 0] );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL0" , Val_Bits [BV{4} 1] );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL1" , Val_Bits [BV{4} 1] );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL2" , Val_Bits [BV{4} 1] );
  (RegColDirect "CFG_ID_AA64PFR0_EL1_EL3" , Val_Bits [BV{4} 1] );
  (RegColDirect "OSLSR_EL1" , Val_Bits [BV{32} 0] );
  (RegColDirect "OSDLR_EL1" , Val_Bits [BV{32} 0] );
  (RegColDirect "EDSCR" , Val_Bits [BV{32} 0] );
  (RegColDirect "MPIDR_EL1" , Val_Bits [BV{64} 0] );
  (RegColStruct "PSTATE" "SP" , Val_Bits [BV{1} 1] );
  (RegColStruct "PSTATE" "EL" , Val_Bits [BV{2} 2] );
  (RegColStruct "PSTATE" "nRW" , Val_Bits [BV{1} 0] );
  (RegColStruct "PSTATE" "D" , Val_Bits [BV{1} 1])
].
