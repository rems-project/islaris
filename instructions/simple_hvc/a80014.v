From isla Require Import opsem.

Definition a80014 : isla_trace :=
  AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "MDCR_EL2" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "MDCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL1" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 55%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPTR_EL2" [] (RegVal_Base (Val_Symbolic 55%Z)) Mk_annot :t:
  Smt (DeclareConst 57%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPTR_EL3" [] (RegVal_Base (Val_Symbolic 57%Z)) Mk_annot :t:
  Smt (DeclareConst 62%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CPACR_EL1" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
  Smt (DeclareConst 66%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CNTHCTL_EL2" [] (RegVal_Base (Val_Symbolic 66%Z)) Mk_annot :t:
  Smt (DeclareConst 69%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL2" [] (RegVal_Base (Val_Symbolic 69%Z)) Mk_annot :t:
  Smt (DeclareConst 72%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "CNTKCTL_EL1" [] (RegVal_Base (Val_Symbolic 72%Z)) Mk_annot :t:
  Smt (DeclareConst 79%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAM2_EL2" [] (RegVal_Base (Val_Symbolic 79%Z)) Mk_annot :t:
  Smt (DeclareConst 90%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICH_HCR_EL2" [] (RegVal_Base (Val_Symbolic 90%Z)) Mk_annot :t:
  Smt (DeclareConst 101%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL1_NS" [] (RegVal_Base (Val_Symbolic 101%Z)) Mk_annot :t:
  Smt (DeclareConst 106%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAMIDR_EL1" [] (RegVal_Base (Val_Symbolic 106%Z)) Mk_annot :t:
  Smt (DeclareConst 118%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "PMUSERENR_EL0" [] (RegVal_Base (Val_Symbolic 118%Z)) Mk_annot :t:
  Smt (DeclareConst 125%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPAM3_EL3" [] (RegVal_Base (Val_Symbolic 125%Z)) Mk_annot :t:
  Smt (DeclareConst 128%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "ICC_SRE_EL3" [] (RegVal_Base (Val_Symbolic 128%Z)) Mk_annot :t:
  Smt (DeclareConst 135%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "MPAMHCR_EL2" [] (RegVal_Base (Val_Symbolic 135%Z)) Mk_annot :t:
  Smt (DeclareConst 150%Z (Ty_BitVec 32%N)) Mk_annot :t:
  ReadReg "HSTR_EL2" [] (RegVal_Base (Val_Symbolic 150%Z)) Mk_annot :t:
  Smt (DeclareConst 168%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 168%Z)) Mk_annot :t:
  Smt (DefineConst 170%Z (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 168%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 170%Z)) Mk_annot :t:
  Smt (DeclareConst 171%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 171%Z)) Mk_annot :t:
  Smt (DefineConst 172%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 171%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 172%Z)) Mk_annot :t:
  tnil
.
