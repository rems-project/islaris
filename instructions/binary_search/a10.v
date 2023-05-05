From isla Require Import opsem.

Definition a10 : isla_trace :=
  AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits (BV 2%N 0x2%Z))) Mk_annot :t:
  AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits (BV 1%N 0x1%Z))) Mk_annot :t:
  Smt (DeclareConst 28%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 28%Z)) Mk_annot :t:
  Smt (DefineConst 48%Z (Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "R29" [] (RegVal_Base (Val_Symbolic 48%Z)) Mk_annot :t:
  Smt (DeclareConst 49%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 49%Z)) Mk_annot :t:
  Smt (DefineConst 50%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 49%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 50%Z)) Mk_annot :t:
  tnil
.
