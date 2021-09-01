From isla Require Import isla_lang.

Definition a7408 : list trc := [
  [
    Smt (DeclareConst 49%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (Val_Symbolic 49%Z) Mk_annot;
    Smt (DefineConst 50%Z (Val (Val_Symbolic 49%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 73%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot; Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot; Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 50%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x1a%Z]) Mk_annot) Mk_annot; Binop ((Bvarith Bvshl)) (Val (Val_Symbolic 50%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x26%Z]) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x3fffffffff%Z]) Mk_annot] Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Symbolic 73%Z) Mk_annot
  ]
].
