From isla Require Import opsem.

Definition a1824c : isla_trace :=
  WriteReg "R6" [] (RegVal_Base (Val_Bits (BV 64%N 0x200000%Z))) Mk_annot :t:
  Smt (DeclareConst 46%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 46%Z)) Mk_annot :t:
  Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 46%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot :t:
  tnil
.
