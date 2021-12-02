From isla Require Import opsem.

Definition a78 : isla_trace :=
  Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot :t:
  ReadReg "PSTATE" [Field "C"] (RegVal_Struct [("C", RegVal_Base (Val_Symbolic 5%Z))]) Mk_annot :t:
  Smt (DefineConst 38%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot :t:
    ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
    Smt (DefineConst 39%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot)) Mk_annot :t:
    tcases [
      Smt (Assert (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot :t:
      WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x0%Z))) Mk_annot :t:
      Smt (DeclareConst 40%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
      Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 40%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
      tnil;
      Smt (Assert (Unop (Not) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot)) Mk_annot :t:
      WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x1%Z))) Mk_annot :t:
      Smt (DeclareConst 40%Z (Ty_BitVec 64%N)) Mk_annot :t:
      ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
      Smt (DefineConst 41%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 40%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
      WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 41%Z)) Mk_annot :t:
      tnil
    ];
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "R0" [] (RegVal_Base (Val_Bits (BV 64%N 0x1%Z))) Mk_annot :t:
    Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
    Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 39%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 40%Z)) Mk_annot :t:
    tnil
  ]
.
