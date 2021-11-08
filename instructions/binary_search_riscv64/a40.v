From isla Require Import opsem.

Definition a40 : isla_trace :=
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 1%N 1%N) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 0%Z)) Mk_annot :t:
  Smt (DefineConst 1%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 13%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x9" [] (RegVal_Base (Val_Symbolic 13%Z)) Mk_annot :t:
  Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x21" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot :t:
  Smt (DefineConst 17%Z (Binop ((Bvcomp Bvsge)) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 13%Z) Mk_annot) Mk_annot) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 14%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 18%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 0%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x38%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  tfork [
    Smt (Assert (Val (Val_Symbolic 17%Z) Mk_annot)) Mk_annot :t:
    Smt (DefineConst 19%Z (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 18%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot :t:
    BranchAddress (RegVal_Base (Val_Symbolic 18%Z)) Mk_annot :t:
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 18%Z)) Mk_annot :t:
    tnil;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 17%Z) Mk_annot) Mk_annot)) Mk_annot :t:
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot :t:
    tnil
  ]
.
