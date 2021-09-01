From isla Require Import isla_lang.

Definition a7430 : list trc := [
  [
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R6" [] (Val_Symbolic 44%Z) Mk_annot;
    Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffff0000ffffffff%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R6" [] (Val_Symbolic 47%Z) Mk_annot
  ]
].
