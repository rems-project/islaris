From isla Require Import opsem.

Definition instr_str : isla_trace :=
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 1%N)) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 26%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "R1" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  Smt (DefineConst 65%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 26%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 66%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R9" [] (RegVal_Base (Val_Symbolic 66%Z)) Mk_annot :t:
  Smt (DefineConst 67%Z (Val (Val_Symbolic 66%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 72%Z (Binop (Eq) (Val (Val_Symbolic 65%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 65%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  Smt (DefineConst 1246%Z (Val (Val_Symbolic 65%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1247%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 1247%Z)) Mk_annot :t:
  Smt (DefineConst 1401%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 65%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1402%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 1401%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1403%Z Ty_Bool) Mk_annot :t:
  WriteMem (RegVal_Base (Val_Symbolic 1403%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 1402%Z)) (RegVal_Base (Val_Symbolic 67%Z)) 8%N None Mk_annot :t:
  Smt (DeclareConst 1404%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 1404%Z)) Mk_annot :t:
  Smt (DefineConst 1405%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1404%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 1405%Z)) Mk_annot :t:
  tnil
.
