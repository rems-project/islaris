From isla Require Import opsem.

Definition a3c : isla_trace :=
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  Smt (DeclareConst 65%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R22" [] (RegVal_Base (Val_Symbolic 65%Z)) Mk_annot :t:
  Smt (DefineConst 66%Z (Val (Val_Symbolic 65%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 67%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 67%Z)) Mk_annot :t:
  Smt (DefineConst 69%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 67%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R30" [] (RegVal_Base (Val_Symbolic 69%Z)) Mk_annot :t:
  Smt (DefineConst 70%Z (Val (Val_Symbolic 66%Z) Mk_annot)) Mk_annot :t:
  BranchAddress (RegVal_Base (Val_Symbolic 70%Z)) Mk_annot :t:
  Smt (DefineConst 71%Z (Val (Val_Symbolic 66%Z) Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 71%Z)) Mk_annot :t:
  tnil
.
