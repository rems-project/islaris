From isla Require Import opsem.

Definition a8016c : isla_trace :=
  Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
  Smt (DefineConst 44%Z (Manyop Concat [Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot; Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 41%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 32%N 0xff%Z)) Mk_annot] Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R0" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DeclareConst 45%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot :t:
  Smt (DefineConst 46%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 46%Z)) Mk_annot :t:
  tnil
.
