From isla Require Import opsem.

Definition a18270 : isla_trace :=
  Smt (DeclareConst 68%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 68%Z)) Mk_annot :t:
  Smt (DefineConst 69%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 68%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 69%Z)) Mk_annot :t:
  tnil
.
