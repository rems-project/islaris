From isla Require Import isla_lang.

Definition a58 : list trc := [
  [
    WriteReg "R23" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 51%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 51%Z)) Mk_annot;
    Smt (DefineConst 52%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 51%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 52%Z)) Mk_annot
  ]
].
