From isla Require Import opsem.

Definition a18220 : isla_trace :=
  AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "MDCR_EL2" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "MDCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits [BV{1%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x501%Z])) Mk_annot :t:
  AssumeReg "SCTLR_EL1" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot :t:
  Smt (DeclareConst 69%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPTR_EL2" [] (RegVal_Base (Val_Symbolic 69%Z)) Mk_annot :t:
  Smt (DeclareConst 71%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPTR_EL3" [] (RegVal_Base (Val_Symbolic 71%Z)) Mk_annot :t:
  Smt (DeclareConst 76%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPACR_EL1" [] (RegVal_Base (Val_Symbolic 76%Z)) Mk_annot :t:
  Smt (DeclareConst 84%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CNTHCTL_EL2" [] (RegVal_Base (Val_Symbolic 84%Z)) Mk_annot :t:
  Smt (DeclareConst 87%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL2" [] (RegVal_Base (Val_Symbolic 87%Z)) Mk_annot :t:
  Smt (DeclareConst 90%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CNTKCTL_EL1" [] (RegVal_Base (Val_Symbolic 90%Z)) Mk_annot :t:
  Smt (DeclareConst 97%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAM2_EL2" [] (RegVal_Base (Val_Symbolic 97%Z)) Mk_annot :t:
  Smt (DeclareConst 108%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICH_HCR_EL2" [] (RegVal_Base (Val_Symbolic 108%Z)) Mk_annot :t:
  Smt (DeclareConst 121%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL1_NS" [] (RegVal_Base (Val_Symbolic 121%Z)) Mk_annot :t:
  Smt (DeclareConst 126%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAMIDR_EL1" [] (RegVal_Base (Val_Symbolic 126%Z)) Mk_annot :t:
  Smt (DeclareConst 140%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "PMUSERENR_EL0" [] (RegVal_Base (Val_Symbolic 140%Z)) Mk_annot :t:
  Smt (DeclareConst 147%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAM3_EL3" [] (RegVal_Base (Val_Symbolic 147%Z)) Mk_annot :t:
  Smt (DeclareConst 150%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL3" [] (RegVal_Base (Val_Symbolic 150%Z)) Mk_annot :t:
  Smt (DeclareConst 157%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "MPAMHCR_EL2" [] (RegVal_Base (Val_Symbolic 157%Z)) Mk_annot :t:
  Smt (DeclareConst 174%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "HSTR_EL2" [] (RegVal_Base (Val_Symbolic 174%Z)) Mk_annot :t:
  Smt (DeclareConst 196%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 196%Z)) Mk_annot :t:
  Smt (DefineConst 197%Z (Val (Val_Symbolic 196%Z) Mk_annot)) Mk_annot :t:
  WriteReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 197%Z)) Mk_annot :t:
  Barrier (RegVal_Base (Val_Enum ((Mk_enum_id 2%nat), Mk_enum_ctor 27%nat))) Mk_annot :t:
  Smt (DeclareConst 227%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 227%Z)) Mk_annot :t:
  Smt (DefineConst 228%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 227%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 228%Z)) Mk_annot :t:
  tnil
.