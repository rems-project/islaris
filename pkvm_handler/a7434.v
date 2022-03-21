From isla Require Import opsem.

Definition a7434 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 16%N)) Mk_annot :t:
  Smt (DeclareConst 90%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R6" [] (RegVal_Base (Val_Symbolic 90%Z)) Mk_annot :t:
  Smt (DefineConst 93%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffff%Z)) Mk_annot] Mk_annot; Binop ((Bvarith Bvshl)) (Unop (ZeroExtend 48%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 64%N 0x30%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R6" [] (RegVal_Base (Val_Symbolic 93%Z)) Mk_annot :t:
  Smt (DeclareConst 94%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 94%Z)) Mk_annot :t:
  Smt (DefineConst 95%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 94%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 95%Z)) Mk_annot :t:
  tnil
.
