From isla Require Import isla_lang.

Definition a4 : list trc := [
  [
    Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot;
    Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 13%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x10" [] (RegVal_Base (Val_Symbolic 13%Z)) Mk_annot;
    Smt (DefineConst 14%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 13%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "x10" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot;
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot
  ]
].
