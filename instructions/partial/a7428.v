From isla Require Import opsem.

Definition a7428 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 2%N)) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 16%N)) Mk_annot :t:
  Smt (DefineConst 169%Z (Unop (SignExtend 64%N) (Unop (Extract 63%N 0%N) (Unop (ZeroExtend 122%N) (Manyop Concat [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot] Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 171%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 171%Z)) Mk_annot :t:
  Smt (DefineConst 174%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 171%Z) Mk_annot; Unop (Bvnot) (Binop ((Bvarith Bvshl)) (Val (Val_Bits [BV{64%N} 0xffff%Z]) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 169%Z) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 48%N) (Val (Val_Symbolic 1%Z) Mk_annot) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 169%Z) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 174%Z)) Mk_annot :t:
  Smt (DeclareConst 175%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 175%Z)) Mk_annot :t:
  Smt (DefineConst 176%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 175%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 176%Z)) Mk_annot :t:
  tnil
.
