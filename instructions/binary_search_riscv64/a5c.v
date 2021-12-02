From isla Require Import opsem.

Definition a5c : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 13%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x18" [] (RegVal_Base (Val_Symbolic 13%Z)) Mk_annot :t:
  Smt (DefineConst 14%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 13%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "x11" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  tnil
.
