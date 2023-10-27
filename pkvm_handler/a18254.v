From isla Require Import opsem.

Definition a18254 : isla_trace :=
  Smt (DeclareConst 31%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R5" [] (RegVal_Base (Val_Symbolic 31%Z)) Mk_annot :t:
  Smt (DeclareConst 33%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R6" [] (RegVal_Base (Val_Symbolic 33%Z)) Mk_annot :t:
  Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 31%Z) Mk_annot; Unop (Bvnot) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R5" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
  Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
  Smt (DefineConst 42%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 41%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot :t:
  tnil
.
