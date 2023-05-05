From isla Require Import opsem.

Definition a60 : isla_trace :=
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
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x38%Z)) Mk_annot] Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  Smt (DefineConst 36%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 26%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x30%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 37%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 41%Z (Binop (Eq) (Val (Val_Symbolic 37%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 37%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  Smt (DefineConst 1216%Z (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1364%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 37%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1365%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 1364%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1366%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 1366%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 1365%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 1369%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x8%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1373%Z (Binop (Eq) (Val (Val_Symbolic 1369%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1369%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2548%Z (Val (Val_Symbolic 1369%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2696%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1369%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2697%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 2696%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2698%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 2698%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 2697%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 2701%Z (Val (Val_Symbolic 1366%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R20" [] (RegVal_Base (Val_Symbolic 2701%Z)) Mk_annot :t:
  Smt (DefineConst 2702%Z (Val (Val_Symbolic 2698%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R19" [] (RegVal_Base (Val_Symbolic 2702%Z)) Mk_annot :t:
  Smt (DeclareConst 2703%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 2703%Z)) Mk_annot :t:
  Smt (DefineConst 2704%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2703%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 2704%Z)) Mk_annot :t:
  tnil
.
