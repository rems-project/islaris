From isla Require Import opsem.

Definition a7428 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 16%N)) Mk_annot :t:
  Smt (DefineConst 136%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot; Unop (ZeroExtend 48%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R6" [] (RegVal_Base (Val_Symbolic 136%Z)) Mk_annot :t:
  Smt (DeclareConst 137%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 137%Z)) Mk_annot :t:
  Smt (DefineConst 138%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 137%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 138%Z)) Mk_annot :t:
  tnil
.
