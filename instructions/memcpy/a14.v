From isla Require Import opsem.

Definition a14 : isla_trace :=
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R2" [] (RegVal_Base (Val_Symbolic 27%Z)) Mk_annot :t:
  Smt (DefineConst 28%Z (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R3" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  Smt (DefineConst 35%Z (Unop (Bvnot) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot; Unop (ZeroExtend 64%N) (Val (Val_Symbolic 35%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 44%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 57%Z (Manyop Concat [Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Bvnot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 44%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits (BV 128%N 0x3f%Z)) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 44%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot; Unop (SignExtend 64%N) (Val (Val_Symbolic 35%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 58%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 57%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 58%Z))]) Mk_annot :t:
  Smt (DefineConst 59%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 57%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 59%Z))]) Mk_annot :t:
  Smt (DefineConst 60%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 57%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 60%Z))]) Mk_annot :t:
  Smt (DefineConst 61%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 57%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 61%Z))]) Mk_annot :t:
  Smt (DeclareConst 62%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
  Smt (DefineConst 63%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 62%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 63%Z)) Mk_annot :t:
  tnil
.
