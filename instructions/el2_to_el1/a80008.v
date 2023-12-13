From isla Require Import opsem.

Definition a80008 : isla_trace :=
  AssumeReg "TCR_EL1" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits (BV 32%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000002%Z))) Mk_annot :t:
  Smt (DeclareConst 26%Z (Ty_BitVec 32%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 4%N 4%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 3%N 2%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 2%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 1%N 1%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 20%N 20%N) (AExp_Val (AVal_Var "SPSR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 55%N 55%N) (AExp_Val (AVal_Var "ELR_EL2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "ELR_EL2" [] (RegVal_Base (Val_Symbolic 27%Z)) Mk_annot :t:
  Smt (DefineConst 30%Z (Unop (Extract 55%N 0%N) (Val (Val_Symbolic 27%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  AbstractPrimop "sail_eret" (RegVal_Unit) [RegVal_Base (Val_Symbolic 30%Z)] Mk_annot :t:
  ReadReg "SPSR_EL2" [] (RegVal_Base (Val_Symbolic 26%Z)) Mk_annot :t:
  WriteReg "PSTATE" [Field "SS"] (RegVal_Struct [("SS", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  Smt (DefineConst 50%Z (Unop (Extract 3%N 2%N) (Val (Val_Symbolic 26%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 76%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 26%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x14%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 76%Z))]) Mk_annot :t:
  WriteReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits (BV 1%N 0x0%Z)))]) Mk_annot :t:
  Smt (DefineConst 80%Z (Unop (Extract 3%N 2%N) (Val (Val_Symbolic 26%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 80%Z))]) Mk_annot :t:
  Smt (DefineConst 82%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 26%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Symbolic 82%Z))]) Mk_annot :t:
  ReadReg "PSTATE" [Field "IL"] (RegVal_Struct [("IL", RegVal_Base (Val_Symbolic 76%Z))]) Mk_annot :t:
  Smt (DefineConst 84%Z (Unop (Extract 31%N 28%N) (Val (Val_Symbolic 26%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 85%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 84%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 85%Z))]) Mk_annot :t:
  Smt (DefineConst 86%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 84%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 86%Z))]) Mk_annot :t:
  Smt (DefineConst 87%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 84%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 87%Z))]) Mk_annot :t:
  Smt (DefineConst 88%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 84%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 88%Z))]) Mk_annot :t:
  Smt (DefineConst 89%Z (Unop (Extract 9%N 6%N) (Val (Val_Symbolic 26%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 90%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 89%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 90%Z))]) Mk_annot :t:
  Smt (DefineConst 91%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 89%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "A"] (RegVal_Struct [("A", RegVal_Base (Val_Symbolic 91%Z))]) Mk_annot :t:
  Smt (DefineConst 92%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 89%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "I"] (RegVal_Struct [("I", RegVal_Base (Val_Symbolic 92%Z))]) Mk_annot :t:
  Smt (DefineConst 93%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 89%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "F"] (RegVal_Struct [("F", RegVal_Base (Val_Symbolic 93%Z))]) Mk_annot :t:
  Smt (DefineConst 95%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 26%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x16%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "PAN"] (RegVal_Struct [("PAN", RegVal_Base (Val_Symbolic 95%Z))]) Mk_annot :t:
  Smt (DeclareConst 96%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 96%Z)) Mk_annot :t:
  WriteReg "EventRegister" [] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Symbolic 80%Z))]) Mk_annot :t:
  Smt (DefineConst 123%Z (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
  BranchAddress (RegVal_Base (Val_Symbolic 123%Z)) Mk_annot :t:
  Smt (DefineConst 124%Z (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 124%Z)) Mk_annot :t:
  tnil
.
