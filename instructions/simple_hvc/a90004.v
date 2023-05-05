From isla Require Import opsem.

Definition a90004 : isla_trace :=
  AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "MDCR_EL2" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 7%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 9%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 10%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 14%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 15%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 18%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 23%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 24%Z (Ty_BitVec 1%N)) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x1%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL1" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 26%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "VBAR_EL2" []) Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0xa0000%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 45%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot :t:
  Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 14%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 24%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 2%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 23%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 15%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Symbolic 18%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 10%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 0%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 9%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 7%Z))]) Mk_annot :t:
  Smt (DefineConst 218%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 14%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 24%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 2%Z) Mk_annot; Val (Val_Symbolic 23%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x1c%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffbfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffdfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 18%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x15%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffefffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 10%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffc3f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 3%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 0%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 9%Z) Mk_annot; Val (Val_Symbolic 7%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x6%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffffffef%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffff3%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x4%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffffe%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "ESR_EL2" [] (RegVal_Base (Val_Bits (BV 32%N 0x5a000000%Z))) Mk_annot :t:
  Smt (DeclareConst 223%Z (Ty_BitVec 64%N)) Mk_annot :t:
  WriteReg "FAR_EL2" [] (RegVal_Base (Val_Symbolic 223%Z)) Mk_annot :t:
  Smt (DeclareConst 224%Z (Ty_BitVec 40%N)) Mk_annot :t:
  Smt (DeclareConst 225%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 225%Z)) Mk_annot :t:
  Smt (DefineConst 226%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 225%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffff0000000000f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 24%N) (Val (Val_Symbolic 224%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 226%Z)) Mk_annot :t:
  WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits (BV 2%N 0x2%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
  WriteReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 218%Z)) Mk_annot :t:
  WriteReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot :t:
  WriteReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  ReadReg "VBAR_EL2" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  Smt (DefineConst 238%Z (Manyop Concat [Unop (Extract 63%N 11%N) (Val (Val_Symbolic 26%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 11%N 0x400%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 239%Z (Val (Val_Symbolic 238%Z) Mk_annot)) Mk_annot :t:
  BranchAddress (RegVal_Base (Val_Symbolic 239%Z)) Mk_annot :t:
  Smt (DefineConst 240%Z (Val (Val_Symbolic 238%Z) Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 240%Z)) Mk_annot :t:
  tnil
.
