From isla Require Import opsem.

Definition a40 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 1%N 1%N) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x9" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x21" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DefineConst 6%Z (Binop ((Bvcomp Bvsge)) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 2%Z) Mk_annot) Mk_annot) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 3%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 7%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x38%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  tcases [
    Smt (Assert (Val (Val_Symbolic 6%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 8%Z (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 7%Z) Mk_annot) (Val (Val_Bits (BV 64%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Symbolic 7%Z)) Mk_annot :t:
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 7%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 6%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
    tnil
  ]
.
