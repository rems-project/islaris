From isla Require Import opsem.

Definition a1822c : isla_trace :=
  Smt (DeclareConst 48%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R2" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot :t:
  Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 48%Z) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 54%Z)) Mk_annot :t:
  Smt (DeclareConst 55%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 55%Z)) Mk_annot :t:
  Smt (DefineConst 56%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 55%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 56%Z)) Mk_annot :t:
  tnil
.