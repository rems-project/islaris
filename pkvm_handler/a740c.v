From isla Require Import isla_lang.

Definition a740c : list trc := [
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (Val_Symbolic 38%Z) Mk_annot;
    Smt (DefineConst 39%Z (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 44%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (ZeroExtend 64%N) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{128%N} 0xffffffffffffffe9%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{128%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 48%Z (Unop (Extract 63%N 0%N) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 61%Z (Manyop Concat [Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Bvnot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 48%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits [BV{128%N} 0x3f%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Val (Val_Symbolic 48%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot) (Val (Val_Symbolic 44%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Ite (Binop (Eq) (Unop (SignExtend 64%N) (Val (Val_Symbolic 48%Z) Mk_annot) Mk_annot) (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvadd) [Unop (SignExtend 64%N) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{128%N} 0xffffffffffffffffffffffffffffffe9%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{128%N} 0x1%Z]) Mk_annot] Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 63%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 61%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "N"] (Val_Struct [("N", Val_Symbolic 17%Z)]) Mk_annot;
    WriteReg "PSTATE" [Field "N"] (Val_Struct [("N", Val_Symbolic 63%Z)]) Mk_annot;
    Smt (DefineConst 64%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 61%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 27%Z)]) Mk_annot;
    WriteReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 64%Z)]) Mk_annot;
    Smt (DefineConst 65%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 61%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    WriteReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 65%Z)]) Mk_annot;
    Smt (DefineConst 66%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 61%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "V"] (Val_Struct [("V", Val_Symbolic 26%Z)]) Mk_annot;
    WriteReg "PSTATE" [Field "V"] (Val_Struct [("V", Val_Symbolic 66%Z)]) Mk_annot
  ]
].
