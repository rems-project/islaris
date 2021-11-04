From isla Require Import opsem.

Definition a50 : isla_trace :=
  AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
  AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot :t:
  Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot :t:
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot :t:
  AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot :t:
  ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot :t:
  Smt (DefineConst 37%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot :t:
  tfork [
    Smt (Assert (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot :t:
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
    Smt (DefineConst 38%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot :t:
    tfork [
      Smt (Assert (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot :t:
      Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
      Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 39%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffdc%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
      ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot :t:
      ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
      ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
      ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
      ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot :t:
      Smt (DefineConst 52%Z (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot :t:
      BranchAddress (RegVal_Base (Val_Symbolic 52%Z)) Mk_annot :t:
      Smt (DefineConst 53%Z (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot :t:
      ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot :t:
      ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot :t:
      ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
      ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot :t:
      tnil;
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
      Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 39%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
      tnil
    ];
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 37%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot :t:
    Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 38%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
    tnil
  ]
.
