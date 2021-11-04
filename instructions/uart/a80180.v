From isla Require Import opsem.

Definition a80180 : isla_trace :=
  Smt (DeclareConst 50%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  Smt (DefineConst 51%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 50%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 51%Z)) Mk_annot :t:
  tnil
.
