From isla Require Import isla_lang.

Definition a8016c : list trc := [
  [
    Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot;
    Smt (DefineConst 56%Z (Manyop Concat [Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot; Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{32%N} 0xff%Z]) Mk_annot] Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R0" [] (RegVal_Base (Val_Symbolic 56%Z)) Mk_annot;
    Smt (DeclareConst 57%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 57%Z)) Mk_annot;
    Smt (DefineConst 58%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 57%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 58%Z)) Mk_annot
  ]
].
