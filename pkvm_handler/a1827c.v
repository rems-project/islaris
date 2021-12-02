From isla Require Import opsem.

Definition a1827c : isla_trace :=
  Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R5" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot :t:
  Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits (BV 64%N 0x798%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R5" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
  Smt (DeclareConst 62%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
  Smt (DefineConst 63%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 62%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 63%Z)) Mk_annot :t:
  tnil
.
