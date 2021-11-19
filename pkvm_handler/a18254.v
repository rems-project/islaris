From isla Require Import opsem.

Definition a18254 : isla_trace :=
  Smt (DeclareConst 48%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R5" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot :t:
  Smt (DeclareConst 50%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R6" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  Smt (DefineConst 57%Z (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 48%Z) Mk_annot; Unop (Bvnot) (Val (Val_Symbolic 50%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R5" [] (RegVal_Base (Val_Symbolic 57%Z)) Mk_annot :t:
  Smt (DeclareConst 58%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 58%Z)) Mk_annot :t:
  Smt (DefineConst 59%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 58%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 59%Z)) Mk_annot :t:
  tnil
.
