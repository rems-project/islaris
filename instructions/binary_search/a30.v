From isla Require Import opsem.

Definition a30 : isla_trace :=
  Smt (DeclareConst 42%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R23" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot :t:
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R8" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DefineConst 75%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 42%Z) Mk_annot) Mk_annot) Mk_annot; Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 44%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "R24" [] (RegVal_Base (Val_Symbolic 75%Z)) Mk_annot :t:
  Smt (DeclareConst 76%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 76%Z)) Mk_annot :t:
  Smt (DefineConst 77%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 76%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 77%Z)) Mk_annot :t:
  tnil
.
