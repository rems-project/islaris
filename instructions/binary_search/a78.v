From isla Require Import opsem.

Definition a78 : isla_trace :=
  Smt (DeclareConst 2%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 24%Z (Ty_BitVec 1%N)) Mk_annot :t:
  ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 2%Z))]) Mk_annot :t:
  Smt (DefineConst 28%Z (Binop (Eq) (Val (Val_Symbolic 2%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 28%Z) Mk_annot)) Mk_annot :t:
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 24%Z))]) Mk_annot :t:
    Smt (DefineConst 29%Z (Binop (Eq) (Val (Val_Symbolic 24%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 29%Z) Mk_annot)) Mk_annot :t:
      WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
      Smt (DeclareConst 30%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 30%Z)) Mk_annot :t:
      Smt (DefineConst 31%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 30%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 31%Z)) Mk_annot :t:
      tnil;
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 29%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x1%Z))) Mk_annot :t:
      Smt (DeclareConst 32%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 32%Z)) Mk_annot :t:
      Smt (DefineConst 33%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 32%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 33%Z)) Mk_annot :t:
      tnil
    ];
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 28%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x1%Z))) Mk_annot :t:
    Smt (DeclareConst 34%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 34%Z)) Mk_annot :t:
    Smt (DefineConst 35%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 34%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 35%Z)) Mk_annot :t:
    tnil
  ]
.
