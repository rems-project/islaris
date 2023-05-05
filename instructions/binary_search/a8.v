From isla Require Import opsem.

Definition a8 : isla_trace :=
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
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x28%Z)) Mk_annot] Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  Smt (DefineConst 36%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 26%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x20%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R22" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot :t:
  Smt (DefineConst 38%Z (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R21" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
  Smt (DefineConst 40%Z (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 46%Z (Binop (Eq) (Val (Val_Symbolic 41%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  Smt (DefineConst 1220%Z (Val (Val_Symbolic 41%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1221%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 1221%Z)) Mk_annot :t:
  Smt (DefineConst 1375%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 41%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1376%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 1375%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1377%Z Ty_Bool) Mk_annot :t:
  WriteMem (RegVal_Base (Val_Symbolic 1377%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 1376%Z)) (RegVal_Base (Val_Symbolic 38%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 1378%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x8%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1383%Z (Binop (Eq) (Val (Val_Symbolic 1378%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1378%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffffff8%Z)) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2557%Z (Val (Val_Symbolic 1378%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2711%Z (Manyop Concat [Val (Val_Bits (BV 4%N 0x0%Z)) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1378%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2712%Z (Unop (ZeroExtend 8%N) (Val (Val_Symbolic 2711%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2713%Z Ty_Bool) Mk_annot :t:
  WriteMem (RegVal_Base (Val_Symbolic 2713%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 2712%Z)) (RegVal_Base (Val_Symbolic 40%Z)) 8%N None Mk_annot :t:
  Smt (DeclareConst 2714%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 2714%Z)) Mk_annot :t:
  Smt (DefineConst 2715%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2714%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 2715%Z)) Mk_annot :t:
  tnil
.
