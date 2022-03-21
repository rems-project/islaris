From isla Require Import opsem.

Definition a18290 : isla_trace :=
  AssumeReg "TCR_EL1" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 32%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 4%N 4%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvxor) [AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot; AExp_Unop (Extract 3%N 3%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 1%N 1%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 20%N 20%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 30%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 55%N 55%N) (AExp_Val (AVal_Var "ELR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 30%Z)) Mk_annot :t:
  Barrier (RegVal_Base (Val_Enum ((Mk_enum_id 2%nat), Mk_enum_ctor 26%nat))) Mk_annot :t:
  ReadReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  WriteReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  Smt (DefineConst 88%Z (Unop (Extract 3%N 2%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 89%Z (Binop (Eq) (Val (Val_Symbolic 88%Z) Mk_annot) (Val (Val_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 89%Z) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 95%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 96%Z (Ty_BitVec 2%N)) Mk_annot :t:
    Smt (DeclareConst 104%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 105%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 113%Z Ty_Bool) Mk_annot :t:
    Smt (DefineConst 118%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 118%Z))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    Smt (DefineConst 122%Z (Unop (Extract 3%N 2%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 122%Z))]) Mk_annot :t:
    Smt (DefineConst 124%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Symbolic 124%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 118%Z))]) Mk_annot :t:
    Smt (DefineConst 126%Z (Unop (Extract 31%N 28%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 127%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 126%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 127%Z))]) Mk_annot :t:
    Smt (DefineConst 128%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 126%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 128%Z))]) Mk_annot :t:
    Smt (DefineConst 129%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 126%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 129%Z))]) Mk_annot :t:
    Smt (DefineConst 130%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 126%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 130%Z))]) Mk_annot :t:
    Smt (DefineConst 131%Z (Unop (Extract 9%N 6%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 132%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 131%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 132%Z))]) Mk_annot :t:
    Smt (DefineConst 133%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 131%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 133%Z))]) Mk_annot :t:
    Smt (DefineConst 134%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 131%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 134%Z))]) Mk_annot :t:
    Smt (DefineConst 135%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 131%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 135%Z))]) Mk_annot :t:
    Smt (DefineConst 137%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 137%Z))]) Mk_annot :t:
    Smt (DeclareConst 138%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 138%Z)) Mk_annot :t:
    Smt (DefineConst 146%Z (Unop (ZeroExtend 96%N) (Manyop Concat [Manyop Concat [Manyop Concat [Unop (Extract 39%N 32%N) (Val (Val_Symbolic 138%Z) Mk_annot) Mk_annot; Unop (Extract 23%N 16%N) (Val (Val_Symbolic 138%Z) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 15%N 8%N) (Val (Val_Symbolic 138%Z) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 7%N 0%N) (Val (Val_Symbolic 138%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "EventRegister" [] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 122%Z))]) Mk_annot :t:
    Smt (DeclareConst 151%Z (Ty_BitVec 1%N)) Mk_annot :t:
    Smt (DeclareConst 152%Z (Ty_BitVec 32%N)) Mk_annot :t:
    Smt (DeclareConst 153%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 154%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 155%Z Ty_Bool) Mk_annot :t:
    Smt (DefineConst 178%Z (Val (Val_Symbolic 30%Z) Mk_annot)) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Symbolic 178%Z)) Mk_annot :t:
    Smt (DefineConst 179%Z (Val (Val_Symbolic 30%Z) Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 179%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 89%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 97%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 98%Z (Ty_BitVec 2%N)) Mk_annot :t:
    Smt (DeclareConst 111%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 116%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 117%Z Ty_Bool) Mk_annot :t:
    Smt (DefineConst 122%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 122%Z))]) Mk_annot :t:
    WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
    Smt (DefineConst 126%Z (Unop (Extract 3%N 2%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 126%Z))]) Mk_annot :t:
    Smt (DefineConst 128%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Symbolic 128%Z))]) Mk_annot :t:
    ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 122%Z))]) Mk_annot :t:
    Smt (DefineConst 130%Z (Unop (Extract 31%N 28%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 131%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 130%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 131%Z))]) Mk_annot :t:
    Smt (DefineConst 132%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 130%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 132%Z))]) Mk_annot :t:
    Smt (DefineConst 133%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 130%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 133%Z))]) Mk_annot :t:
    Smt (DefineConst 134%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 130%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 134%Z))]) Mk_annot :t:
    Smt (DefineConst 135%Z (Unop (Extract 9%N 6%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 136%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 135%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 136%Z))]) Mk_annot :t:
    Smt (DefineConst 137%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 135%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 137%Z))]) Mk_annot :t:
    Smt (DefineConst 138%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 135%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 138%Z))]) Mk_annot :t:
    Smt (DefineConst 139%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 135%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 139%Z))]) Mk_annot :t:
    Smt (DefineConst 141%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 141%Z))]) Mk_annot :t:
    Smt (DeclareConst 142%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 142%Z)) Mk_annot :t:
    Smt (DefineConst 149%Z (Manyop Concat [Manyop Concat [Manyop Concat [Unop (Extract 39%N 32%N) (Val (Val_Symbolic 142%Z) Mk_annot) Mk_annot; Unop (Extract 23%N 16%N) (Val (Val_Symbolic 142%Z) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 15%N 8%N) (Val (Val_Symbolic 142%Z) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 7%N 0%N) (Val (Val_Symbolic 142%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "EventRegister" [] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 126%Z))]) Mk_annot :t:
    Smt (DeclareConst 159%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 162%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 163%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 164%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 178%Z Ty_Bool) Mk_annot :t:
    Smt (DeclareConst 179%Z Ty_Bool) Mk_annot :t:
    Smt (DefineConst 195%Z (Val (Val_Symbolic 30%Z) Mk_annot)) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Symbolic 195%Z)) Mk_annot :t:
    Smt (DefineConst 196%Z (Val (Val_Symbolic 30%Z) Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 196%Z)) Mk_annot :t:
    tnil
  ]
.
