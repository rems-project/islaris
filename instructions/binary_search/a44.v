From isla Require Import opsem.

Definition a44 : isla_trace :=
  Smt (DeclareConst 24%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 27%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R20" [] (RegVal_Base (Val_Symbolic 27%Z)) Mk_annot :t:
  Smt (DefineConst 28%Z (Val (Val_Symbolic 27%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R24" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot :t:
  Smt (DefineConst 30%Z (Val (Val_Symbolic 29%Z) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 24%Z))]) Mk_annot :t:
  Smt (DefineConst 33%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 24%Z) Mk_annot) (Val (Val_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 33%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 34%Z (Val (Val_Symbolic 28%Z) Mk_annot)) Mk_annot :t:
    WriteReg "R20" [] (RegVal_Base (Val_Symbolic 34%Z)) Mk_annot :t:
    Smt (DeclareConst 35%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 35%Z)) Mk_annot :t:
    Smt (DefineConst 36%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 35%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 36%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 33%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 37%Z (Val (Val_Symbolic 30%Z) Mk_annot)) Mk_annot :t:
    WriteReg "R20" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot :t:
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot :t:
    Smt (DefineConst 39%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 38%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
    tnil
  ]
.
