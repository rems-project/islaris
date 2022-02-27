From isla Require Import opsem.

Definition a58 : isla_trace :=
  WriteReg "R23" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
  Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot :t:
  Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 53%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 54%Z)) Mk_annot :t:
  tnil
.
