From isla Require Import opsem.

Definition a18 : isla_trace :=
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
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "R1" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0xfff0000000000000%Z]) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  Smt (DefineConst 87%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 91%Z (Binop (Eq) (Val (Val_Symbolic 87%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 87%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot :t:
  Smt (DeclareConst 1316%Z (Ty_BitVec 56%N)) Mk_annot :t:
  Smt (DefineConst 1325%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 87%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 1326%Z (Ty_BitVec 8%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 1326%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 1325%Z)) 1%N None Mk_annot :t:
  Smt (DefineConst 1330%Z (Manyop Concat [Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot; Manyop Concat [Val (Val_Bits [BV{24%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 1326%Z) Mk_annot] Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 1330%Z)) Mk_annot :t:
  Smt (DefineConst 1331%Z (Val (Val_Symbolic 87%Z) Mk_annot)) Mk_annot :t:
  WriteReg "R1" [] (RegVal_Base (Val_Symbolic 1331%Z)) Mk_annot :t:
  Smt (DeclareConst 1332%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 1332%Z)) Mk_annot :t:
  Smt (DefineConst 1333%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1332%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 1333%Z)) Mk_annot :t:
  tnil
.
