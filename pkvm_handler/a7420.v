From isla Require Import opsem.

Definition a7420 : isla_trace :=
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits [BV{1%N} 0x1%Z])) Mk_annot :t:
  Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot :t:
  Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits [BV{64%N} 0x10%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
  Smt (DeclareConst 62%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
  Smt (DefineConst 63%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 62%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 63%Z)) Mk_annot :t:
  tnil
.
