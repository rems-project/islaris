From isla Require Import opsem.

Definition a40 : isla_trace :=
  Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R0" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot :t:
  Smt (DefineConst 55%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot; Val (Val_Bits (BV 32%N 0x1%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 57%Z (Manyop (Bvmanyarith Bvor) [Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 55%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x1f%Z)) Mk_annot) Mk_annot) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DefineConst 58%Z (Binop (Eq) (Val (Val_Symbolic 55%Z) Mk_annot) (Val (Val_Bits (BV 32%N 0x0%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 58%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 60%Z (Manyop Concat [Manyop Concat [Val (Val_Symbolic 57%Z) Mk_annot; Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    Smt (DefineConst 61%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 61%Z))]) Mk_annot :t:
    Smt (DefineConst 62%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 62%Z))]) Mk_annot :t:
    Smt (DefineConst 63%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 63%Z))]) Mk_annot :t:
    Smt (DefineConst 64%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 64%Z))]) Mk_annot :t:
    Smt (DeclareConst 65%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 65%Z)) Mk_annot :t:
    Smt (DefineConst 66%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 65%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 66%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 58%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 60%Z (Manyop Concat [Manyop Concat [Val (Val_Symbolic 57%Z) Mk_annot; Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot] Mk_annot; Val (Val_Bits (BV 2%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    Smt (DefineConst 61%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 61%Z))]) Mk_annot :t:
    Smt (DefineConst 62%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 62%Z))]) Mk_annot :t:
    Smt (DefineConst 63%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 63%Z))]) Mk_annot :t:
    Smt (DefineConst 64%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 64%Z))]) Mk_annot :t:
    Smt (DeclareConst 65%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 65%Z)) Mk_annot :t:
    Smt (DefineConst 66%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 65%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 66%Z)) Mk_annot :t:
    tnil
  ]
.
