From isla Require Import isla_lang.

Definition a741c : list trc := [
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 28%Z (Ty_BitVec 1%N)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    Smt (DefineConst 37%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12137:4 - 12139:5" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot;
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (Val_Symbolic 38%Z) Mk_annot;
    Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 38%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffff3e4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Symbolic 28%Z)]) Mk_annot;
    Smt (DefineConst 51%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 54%Z (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot;
    BranchAddress (Val_Symbolic 54%Z) Mk_annot;
    Smt (DefineConst 55%Z (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 56%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
    ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
    ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
    WriteReg "_PC" [] (Val_Symbolic 55%Z) Mk_annot;
    WriteReg "__PC_changed" [] (Val_Bool true) Mk_annot
  ];
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    Smt (DefineConst 37%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 12137:4 - 12139:5" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 37%Z) Mk_annot) Mk_annot)) Mk_annot
  ]
].
