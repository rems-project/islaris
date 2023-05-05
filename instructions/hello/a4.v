From isla Require Import opsem.

Definition a4 : isla_trace :=
  WriteReg "R2" [] (RegVal_Base (Val_Bits (BV 64%N 0x1000%Z))) Mk_annot :t:
  Smt (DeclareConst 32%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 32%Z)) Mk_annot :t:
  Smt (DefineConst 33%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 32%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 33%Z)) Mk_annot :t:
  tnil
.
