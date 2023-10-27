From isla Require Import opsem.

Definition a0 : isla_trace :=
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 27%Z)) Mk_annot :t:
  Smt (DefineConst 30%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 27%Z) Mk_annot; Val (Val_Bits (BV 64%N 0xfffffffffffff000%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R1" [] (RegVal_Base (Val_Symbolic 30%Z)) Mk_annot :t:
  Smt (DefineConst 31%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 27%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 31%Z)) Mk_annot :t:
  tnil
.
