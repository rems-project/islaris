From isla Require Import isla_lang.

Definition a8019c : list trc := [
  [
    Smt (DeclareConst 50%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot;
    Smt (DefineConst 51%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 50%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 51%Z)) Mk_annot
  ]
].
