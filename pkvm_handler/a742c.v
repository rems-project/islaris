From isla Require Import opsem.

Definition a742c : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 16%N)) Mk_annot :t:
  Smt (DeclareConst 78%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R6" [] (RegVal_Base (Val_Symbolic 78%Z)) Mk_annot :t:
  Smt (DefineConst 81%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffff0000ffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 48%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x10%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R6" [] (RegVal_Base (Val_Symbolic 81%Z)) Mk_annot :t:
  Smt (DeclareConst 82%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 82%Z)) Mk_annot :t:
  Smt (DefineConst 83%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 82%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 83%Z)) Mk_annot :t:
  tnil
.
