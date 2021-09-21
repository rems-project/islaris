From isla Require Import isla_lang.

Definition a40 : list trc := [
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot;
    Smt (DefineConst 55%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{32%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 58%Z (Binop (Eq) (Val (Val_Symbolic 55%Z) Mk_annot) (Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 4039:4 - 4039:34" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 58%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 60%Z (Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Bvnot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 55%Z) Mk_annot) (Unop (Extract 31%N 0%N) (Val (Val_Bits [BV{128%N} 0x1f%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{2%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 61%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 17%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 61%Z))]) Mk_annot;
    Smt (DefineConst 62%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 62%Z))]) Mk_annot;
    Smt (DefineConst 63%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 63%Z))]) Mk_annot;
    Smt (DefineConst 64%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 64%Z))]) Mk_annot
  ];
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot;
    Smt (DefineConst 55%Z (Manyop (Bvmanyarith Bvand) [Unop (Extract 31%N 0%N) (Val (Val_Symbolic 53%Z) Mk_annot) Mk_annot; Val (Val_Bits [BV{32%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 58%Z (Binop (Eq) (Val (Val_Symbolic 55%Z) Mk_annot) (Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 4039:4 - 4039:34" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 58%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 60%Z (Manyop Concat [Manyop Concat [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot; Unop (Bvnot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot] Mk_annot; Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 55%Z) Mk_annot) (Unop (Extract 31%N 0%N) (Val (Val_Bits [BV{128%N} 0x1f%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot] Mk_annot; Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{2%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 61%Z (Unop (Extract 3%N 3%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 17%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "N"] (RegVal_Struct [("N", RegVal_Base (Val_Symbolic 61%Z))]) Mk_annot;
    Smt (DefineConst 62%Z (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 62%Z))]) Mk_annot;
    Smt (DefineConst 63%Z (Unop (Extract 1%N 1%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 63%Z))]) Mk_annot;
    Smt (DefineConst 64%Z (Unop (Extract 0%N 0%N) (Val (Val_Symbolic 60%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 26%Z))]) Mk_annot;
    WriteReg "PSTATE" [Field "V"] (RegVal_Struct [("V", RegVal_Base (Val_Symbolic 64%Z))]) Mk_annot
  ]
].
