From isla Require Import isla_lang.

Definition a7c : list trc := [
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 42%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R8" [] (RegVal_Base (Val_Symbolic 42%Z)) Mk_annot;
    Smt (DefineConst 43%Z (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot;
    Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R9" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot;
    Smt (DefineConst 50%Z (Unop (Bvnot) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 54%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 43%Z) Mk_annot) Mk_annot; Unop (ZeroExtend 64%N) (Val (Val_Symbolic 50%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{128%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 59%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 72%Z (Manyop Concat [Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Bvnot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 59%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits [BV{128%N} 0x3f%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 59%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 59%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 54%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 59%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 43%Z) Mk_annot) Mk_annot; Unop (SignExtend 64%N) (Val (Val_Symbolic 50%Z) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{128%N} 0x1%Z]) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 74%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 17%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 74%Z))]) Mk_annot;
    Smt (DefineConst 75%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 75%Z))]) Mk_annot;
    Smt (DefineConst 76%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 76%Z))]) Mk_annot;
    Smt (DefineConst 77%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 72%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 77%Z))]) Mk_annot
  ]
].
