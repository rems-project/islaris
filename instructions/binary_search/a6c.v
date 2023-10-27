From isla Require Import opsem.

Definition a6c : isla_trace :=
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
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 26%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x8%Z)) Mk_annot] Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  Smt (DefineConst 35%Z (Val (Val_Symbolic 26%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 36%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 35%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 40%Z (Binop (Eq) (Val (Val_Symbolic 36%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  Smt (DefineConst 1215%Z (Val (Val_Symbolic 36%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1363%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1364%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 1363%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1365%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 1365%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 1364%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 1368%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 35%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x8%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1372%Z (Binop (Eq) (Val (Val_Symbolic 1368%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1368%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2547%Z (Val (Val_Symbolic 1368%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2695%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1368%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2696%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 2695%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2697%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 2697%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 2696%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 2700%Z (Val (Val_Symbolic 1365%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R29" [] (RegVal_Base (Val_Symbolic 2700%Z)) Mk_annot :t:
  Smt (DefineConst 2701%Z (Val (Val_Symbolic 2697%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R30" [] (RegVal_Base (Val_Symbolic 2701%Z)) Mk_annot :t:
  Smt (DefineConst 2703%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 35%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x40%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 2703%Z)) Mk_annot :t:
  Smt (DeclareConst 2704%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 2704%Z)) Mk_annot :t:
  Smt (DefineConst 2705%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2704%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 2705%Z)) Mk_annot :t:
  tnil
.
