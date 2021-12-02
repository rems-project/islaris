From isla Require Import opsem.

Definition instr_str_unaligned : isla_trace :=
  AssumeReg "VBAR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 10%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 12%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 13%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 18%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 21%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "R1" []) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0xfff0000000000007%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  Smt (DefineConst 90%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 91%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 91%Z)) Mk_annot :t:
  Smt (DeclareConst 106%Z Ty_Bool) Mk_annot :t:
  Smt (DeclareConst 139%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 139%Z)) Mk_annot :t:
  Smt (DefineConst 140%Z (Val (Val_Symbolic 139%Z) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 106%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 214%Z (Val (Val_Symbolic 90%Z) Mk_annot)) Mk_annot :t:
    ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 17%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 18%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Symbolic 21%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 13%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 12%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 10%Z))]) Mk_annot :t:
    Smt (DefineConst 241%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 17%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 27%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 5%Z) Mk_annot; Val (Val_Symbolic 26%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x1c%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffbfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 18%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffdfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 21%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x15%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffefffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 13%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffc3f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 6%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 3%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 12%Z) Mk_annot; Val (Val_Symbolic 10%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x6%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffffffef%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffff3%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x8%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffffe%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "ESR_EL2" [] (RegVal_Base (Val_Bits (BV 32%N 0x960000e1%Z))) Mk_annot :t:
    WriteReg "FAR_EL2" [] (RegVal_Base (Val_Symbolic 214%Z)) Mk_annot :t:
    Smt (DeclareConst 248%Z (Ty_BitVec 40%N)) Mk_annot :t:
    Smt (DeclareConst 249%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 249%Z)) Mk_annot :t:
    Smt (DefineConst 250%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 249%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffff0000000000f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 24%N) (Val (Val_Symbolic 248%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 250%Z)) Mk_annot :t:
    WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits (BV 2%N 0x2%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 241%Z)) Mk_annot :t:
    WriteReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 140%Z)) Mk_annot :t:
    WriteReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    Barrier (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 25%nat))) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Bits (BV 64%N 0x200%Z))) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Bits (BV 64%N 0x200%Z))) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 106%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 214%Z (Val (Val_Symbolic 90%Z) Mk_annot)) Mk_annot :t:
    ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 17%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 18%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Symbolic 21%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 13%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 3%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 12%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 10%Z))]) Mk_annot :t:
    Smt (DefineConst 241%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 17%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 27%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 5%Z) Mk_annot; Val (Val_Symbolic 26%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x1c%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffbfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 18%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffdfffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 21%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x15%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffefffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 31%N) (Val (Val_Symbolic 13%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffc3f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 28%N) (Manyop Concat [Val (Val_Symbolic 6%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 3%Z) Mk_annot; Manyop Concat [Val (Val_Symbolic 12%Z) Mk_annot; Val (Val_Symbolic 10%Z) Mk_annot] Mk_annot] Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x6%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xffffffef%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffff3%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x8%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0xfffffffe%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 32%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "ESR_EL2" [] (RegVal_Base (Val_Bits (BV 32%N 0x96000061%Z))) Mk_annot :t:
    WriteReg "FAR_EL2" [] (RegVal_Base (Val_Symbolic 214%Z)) Mk_annot :t:
    Smt (DeclareConst 248%Z (Ty_BitVec 40%N)) Mk_annot :t:
    Smt (DeclareConst 249%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 249%Z)) Mk_annot :t:
    Smt (DefineConst 250%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 249%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffff0000000000f%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 24%N) (Val (Val_Symbolic 248%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "HPFAR_EL2" [] (RegVal_Base (Val_Symbolic 250%Z)) Mk_annot :t:
    WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits (BV 2%N 0x2%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 241%Z)) Mk_annot :t:
    WriteReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 140%Z)) Mk_annot :t:
    WriteReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Bits (BV 1%N 0x1%Z)))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    Barrier (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 25%nat))) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Bits (BV 64%N 0x200%Z))) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Bits (BV 64%N 0x200%Z))) Mk_annot :t:
    tnil
  ]
.
