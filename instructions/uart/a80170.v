From isla Require Import opsem.

Definition a80170 : isla_trace :=
  Smt (DeclareConst 32%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R2" [] (RegVal_Base (Val_Symbolic 32%Z)) Mk_annot :t:
  Smt (DefineConst 35%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 32%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xffffffff0000ffff%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x3f210000%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R2" [] (RegVal_Base (Val_Symbolic 35%Z)) Mk_annot :t:
  Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 36%Z)) Mk_annot :t:
  Smt (DefineConst 37%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 36%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot :t:
  tnil
.
