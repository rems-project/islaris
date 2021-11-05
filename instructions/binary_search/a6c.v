From isla Require Import opsem.

Definition a6c : isla_trace :=
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits [BV{1%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "SP_EL2" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits [BV{1%N} 0x1%Z]))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  ReadReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot :t:
  Smt (DefineConst 72%Z (Val (Val_Symbolic 29%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 73%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 72%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 77%Z (Binop (Eq) (Val (Val_Symbolic 73%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 77%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 77%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 73%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot :t:
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot :t:
  ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
  ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 73%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 77%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot :t:
  ReadReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  ReadReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  ReadReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot :t:
  Smt (DeclareConst 1318%Z (Ty_BitVec 56%N)) Mk_annot :t:
  Smt (DefineConst 1327%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 73%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1328%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 1328%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 1327%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 1331%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 72%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 1335%Z (Binop (Eq) (Val (Val_Symbolic 1331%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1331%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1335%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1335%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 1331%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1331%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 1331%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1335%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 2555%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1331%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2556%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 2556%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 2555%Z)) 8%N None Mk_annot :t:
  Smt (DefineConst 2559%Z (Val (Val_Symbolic 1328%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R29" [] (RegVal_Base (Val_Symbolic 2559%Z)) Mk_annot :t:
  Smt (DefineConst 2560%Z (Val (Val_Symbolic 2556%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R30" [] (RegVal_Base (Val_Symbolic 2560%Z)) Mk_annot :t:
  Smt (DefineConst 2562%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 72%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x40%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 2562%Z)) Mk_annot :t:
  Smt (DeclareConst 2563%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 2563%Z)) Mk_annot :t:
  Smt (DefineConst 2564%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 2563%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 2564%Z)) Mk_annot :t:
  tnil
.
