From isla Require Import opsem.

Definition a48 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 10%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x10" [] (RegVal_Base (Val_Symbolic 10%Z)) Mk_annot :t:
  Smt (DefineConst 11%Z (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 10%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x1%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "x10" [] (RegVal_Base (Val_Symbolic 11%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  tnil
.
