From isla Require Import opsem.

Definition a40 : isla_trace :=
  Smt (DeclareConst 41%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
  Smt (DefineConst 43%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 41%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 32%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 45%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 43%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x1f%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 46%Z (Binop (Eq) (Val (Val_Symbolic 43%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 46%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 48%Z (Manyop Concat [Manyop Concat [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    Smt (DefineConst 49%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 49%Z))]) Mk_annot :t:
    Smt (DefineConst 50%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 50%Z))]) Mk_annot :t:
    Smt (DefineConst 51%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 51%Z))]) Mk_annot :t:
    Smt (DefineConst 52%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 52%Z))]) Mk_annot :t:
    Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot :t:
    Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 53%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 54%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 46%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 56%Z (Manyop Concat [Manyop Concat [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    Smt (DefineConst 57%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 57%Z))]) Mk_annot :t:
    Smt (DefineConst 58%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 58%Z))]) Mk_annot :t:
    Smt (DefineConst 59%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 59%Z))]) Mk_annot :t:
    Smt (DefineConst 60%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 56%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 60%Z))]) Mk_annot :t:
    Smt (DeclareConst 61%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot :t:
    Smt (DefineConst 62%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 61%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 62%Z)) Mk_annot :t:
    tnil
  ]
.
