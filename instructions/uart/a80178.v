From isla Require Import isla_lang.

Definition a80178 : list trc := [
  [
    Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 36%Z)) Mk_annot;
    Smt (DefineConst 40%Z (Binop (Eq) (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{32%N} 0x5%Z]) Mk_annot) Mk_annot) Mk_annot] Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12129:4 - 12131:5" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 40%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot;
    Smt (DefineConst 42%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot
  ];
  [
    AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot;
    AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 36%Z)) Mk_annot;
    Smt (DefineConst 40%Z (Binop (Eq) (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{32%N} 0x5%Z]) Mk_annot) Mk_annot) Mk_annot] Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12129:4 - 12131:5" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot;
    Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot;
    Smt (DefineConst 42%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x14%Z]) Mk_annot] Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    Smt (DefineConst 54%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot;
    BranchAddress (RegVal_Base (Val_Symbolic 54%Z)) Mk_annot;
    Smt (DefineConst 55%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 55%Z)) Mk_annot
  ]
].
