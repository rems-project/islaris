From isla Require Import opsem.

Definition a1827c : isla_trace :=
  Smt (DeclareConst 28%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R5" [] (RegVal_Base (Val_Symbolic 28%Z)) Mk_annot :t:
  Smt (DefineConst 50%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits (BV 64%N 0x798%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R5" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  Smt (DeclareConst 51%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 51%Z)) Mk_annot :t:
  Smt (DefineConst 52%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 51%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 52%Z)) Mk_annot :t:
  tnil
.
