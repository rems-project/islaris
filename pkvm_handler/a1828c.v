From isla Require Import opsem.

Definition a1828c : isla_trace :=
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffffffff0000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0xca11%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot :t:
  Smt (DeclareConst 48%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot :t:
  Smt (DefineConst 49%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 48%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 49%Z)) Mk_annot :t:
  tnil
.
