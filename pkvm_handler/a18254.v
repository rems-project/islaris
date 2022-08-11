From isla Require Import opsem.

Definition a18254 : isla_trace :=
  Smt (DeclareConst 50%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R5" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  Smt (DeclareConst 52%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R6" [] (RegVal_Base (Val_Symbolic 52%Z)) Mk_annot :t:
  Smt (DefineConst 59%Z (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 50%Z) Mk_annot; Unop (Bvnot) (Val (Val_Symbolic 52%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R5" [] (RegVal_Base (Val_Symbolic 59%Z)) Mk_annot :t:
  Smt (DeclareConst 60%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 60%Z)) Mk_annot :t:
  Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 60%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
  tnil
.
