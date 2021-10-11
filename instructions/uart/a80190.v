From isla Require Import isla_lang.

Definition a80190 : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot;
    Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffff0000ffff%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x3f210000%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R1" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot
  ]
].
