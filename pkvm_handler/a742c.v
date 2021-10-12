From isla Require Import isla_lang.

Definition a742c : list trc := [
  [
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R6" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot;
    Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffff0000ffff%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R6" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot;
    Smt (DeclareConst 48%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot;
    Smt (DefineConst 49%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 48%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 49%Z)) Mk_annot
  ]
].
