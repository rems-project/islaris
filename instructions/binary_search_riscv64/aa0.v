From isla Require Import opsem.

Definition aa0 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 17%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x11" [] (RegVal_Base (Val_Symbolic 17%Z)) Mk_annot :t:
  Smt (DeclareConst 18%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x10" [] (RegVal_Base (Val_Symbolic 18%Z)) Mk_annot :t:
  Smt (DefineConst 23%Z (Unop (ZeroExtend 63%N) (Ite (Binop ((Bvcomp Bvslt)) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 17%Z) Mk_annot) Mk_annot) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 18%Z) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "x10" [] (RegVal_Base (Val_Symbolic 23%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
  tnil
.
