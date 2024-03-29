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
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R22" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DefineConst 45%Z (Val (Val_Symbolic 44%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 46%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 46%Z)) Mk_annot :t:
  Smt (DefineConst 48%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 46%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R30" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot :t:
  Smt (DefineConst 49%Z (Val (Val_Symbolic 45%Z) Mk_annot)) Mk_annot :t:
  BranchAddress (RegVal_Base (Val_Symbolic 49%Z)) Mk_annot :t:
  Smt (DefineConst 50%Z (Val (Val_Symbolic 45%Z) Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  tnil
.
