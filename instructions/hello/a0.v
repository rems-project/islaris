From isla Require Import isla_lang.

Definition a0 : list trc := [
  [
    Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot;
    Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 37%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffff000%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R1" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot;
    Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 37%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot
  ]
].
