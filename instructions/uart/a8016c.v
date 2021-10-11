From isla Require Import isla_lang.

Definition a8016c : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot;
    Smt (DefineConst 56%Z (Manyop Concat [Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot; Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{32%N} 0xff%Z]) Mk_annot] Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R0" [] (RegVal_Base (Val_Symbolic 56%Z)) Mk_annot
  ]
].
