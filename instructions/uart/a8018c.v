From isla Require Import isla_lang.

Definition a8018c : list trc := [
  [
    WriteReg "R1" [] (RegVal_Base (Val_Bits [BV{64%N} 0x5040%Z])) Mk_annot;
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot;
    Smt (DefineConst 45%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot
  ]
].
