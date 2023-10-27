From isla Require Import opsem.

Definition a18230 : isla_trace :=
  Smt (DeclareConst 31%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R3" [] (RegVal_Base (Val_Symbolic 31%Z)) Mk_annot :t:
  Smt (DefineConst 37%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot; Val (Val_Symbolic 31%Z) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R1" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot :t:
  Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot :t:
  Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 38%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
  tnil
.
