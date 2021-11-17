From isla Require Import opsem.

Definition a44 : isla_trace :=
  Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot :t:
  Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R20" [] (RegVal_Base (Val_Symbolic 37%Z)) Mk_annot :t:
  Smt (DefineConst 38%Z (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "R24" [] (RegVal_Base (Val_Symbolic 39%Z)) Mk_annot :t:
  Smt (DefineConst 40%Z (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot :t:
  ReadReg "PSTATE" [Field "Z"] (RegVal_Struct [("Z", RegVal_Base (Val_Symbolic 27%Z))]) Mk_annot :t:
  Smt (DefineConst 43%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 43%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 44%Z (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot :t:
    WriteReg "R20" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
    Smt (DeclareConst 45%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot :t:
    Smt (DefineConst 46%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 46%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 43%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 44%Z (Val (Val_Symbolic 40%Z) Mk_annot)) Mk_annot :t:
    WriteReg "R20" [] (RegVal_Base (Val_Symbolic 44%Z)) Mk_annot :t:
    Smt (DeclareConst 45%Z (Ty_BitVec 64%N)) Mk_annot :t:
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 45%Z)) Mk_annot :t:
    Smt (DefineConst 46%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 45%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 46%Z)) Mk_annot :t:
    tnil
  ]
.
