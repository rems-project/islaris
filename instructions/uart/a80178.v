From isla Require Import opsem.

Definition a80178 : isla_trace :=
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits (BV 4%N 0x1%Z))) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits (BV 1%N 0x0%Z))) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits (BV 32%N 0x501%Z))) Mk_annot :t:
  Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 36%Z)) Mk_annot :t:
  Smt (DefineConst 40%Z (Binop (Eq) (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 32%N 0x5%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
    Smt (DefineConst 42%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x14%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    Smt (DefineConst 54%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Symbolic 54%Z)) Mk_annot :t:
    Smt (DefineConst 55%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 55%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 40%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
    Smt (DefineConst 42%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot :t:
    tnil
  ]
.
