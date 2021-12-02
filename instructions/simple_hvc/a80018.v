From isla Require Import opsem.

Definition a80018 : isla_trace :=
  WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x90000%Z))) Mk_annot :t:
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DefineConst 45%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot :t:
  tnil
.
