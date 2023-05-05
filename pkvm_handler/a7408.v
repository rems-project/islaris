From isla Require Import opsem.

Definition a7408 : isla_trace :=
  Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
  Smt (DefineConst 40%Z (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 60%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot; Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot; Manyop (Bvmanyarith Bvand) [Manyop (Bvmanyarith Bvor) [Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 40%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x1a%Z)) Mk_annot) Mk_annot; Binop ((Bvarith Bvshl)) (Val (Val_Symbolic 40%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x26%Z)) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffffffff%Z)) Mk_annot] Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x3fffffffff%Z)) Mk_annot] Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 60%Z)) Mk_annot :t:
  Smt (DeclareConst 61%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
  Smt (DefineConst 62%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 61%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
  tnil
.
