From isla Require Import opsem.

Definition a74 : isla_trace :=
  Smt (DeclareConst 42%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot :t:
  Smt (DefineConst 43%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R1" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
  Smt (DefineConst 50%Z (Unop (Bvnot) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 43%Z) Mk_annot) Mk_annot; Unop (ZeroExtend 64%N) (Val (Val_Symbolic 50%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 59%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 72%Z (Manyop Concat [Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Bvnot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 59%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits (BV 128%N 0x3f%Z)) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 59%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 59%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 59%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 43%Z) Mk_annot) Mk_annot; Unop (SignExtend 64%N) (Val (Val_Symbolic 50%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits (BV 128%N 0x1%Z)) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 74%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 74%Z))]) Mk_annot :t:
  Smt (DefineConst 75%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 75%Z))]) Mk_annot :t:
  Smt (DefineConst 76%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 76%Z))]) Mk_annot :t:
  Smt (DefineConst 77%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 77%Z))]) Mk_annot :t:
  Smt (DeclareConst 78%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 78%Z)) Mk_annot :t:
  Smt (DefineConst 79%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 79%Z)) Mk_annot :t:
  tnil
.
