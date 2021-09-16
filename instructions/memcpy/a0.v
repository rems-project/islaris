From isla Require Import isla_lang.

Definition a0 : list trc := [
  [
    Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R2" [] (Val_Symbolic 36%Z) Mk_annot;
    Smt (DefineConst 39%Z (Binop (Eq) (Binop (Eq) (Val (Val_Symbolic 36%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) (Val (Val_Bool true) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12148:4 - 12150:5" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot;
    Smt (DeclareConst 40%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (Val_Symbolic 40%Z) Mk_annot;
    Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 40%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x1c%Z]) Mk_annot] Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Bits [BV{1%N} 0x0%Z])]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    Smt (DefineConst 53%Z (Val (Val_Symbolic 41%Z) Mk_annot)) Mk_annot;
    BranchAddress (Val_Symbolic 53%Z) Mk_annot;
    Smt (DefineConst 54%Z (Val (Val_Symbolic 41%Z) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
    ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
    WriteReg "_PC" [] (Val_Symbolic 54%Z) Mk_annot;
    WriteReg "__PC_changed" [] (Val_Bool true) Mk_annot
  ];
  [
    Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R2" [] (Val_Symbolic 36%Z) Mk_annot;
    Smt (DefineConst 39%Z (Binop (Eq) (Binop (Eq) (Val (Val_Symbolic 36%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) (Val (Val_Bool true) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12148:4 - 12150:5" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot)) Mk_annot
  ]
].
