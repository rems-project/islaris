From isla Require Import opsem.

Definition a7418 : isla_trace :=
  Smt (DeclareConst 28%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 28%Z)) Mk_annot :t:
  Smt (DefineConst 29%Z (Val (Val_Symbolic 28%Z) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 34%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 128%N 0xfffffffffffffffc%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 38%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 34%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 51%Z (Manyop Concat [Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Bvnot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 38%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits (BV 128%N 0x3f%Z)) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 38%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 34%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 128%N 0xfffffffffffffffffffffffffffffffc%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 52%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 52%Z))]) Mk_annot :t:
  Smt (DefineConst 53%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 53%Z))]) Mk_annot :t:
  Smt (DefineConst 54%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 54%Z))]) Mk_annot :t:
  Smt (DefineConst 55%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 51%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 55%Z))]) Mk_annot :t:
  Smt (DeclareConst 56%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 56%Z)) Mk_annot :t:
  Smt (DefineConst 57%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 56%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 57%Z)) Mk_annot :t:
  tnil
.
