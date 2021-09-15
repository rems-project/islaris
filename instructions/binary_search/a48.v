From isla Require Import isla_lang.

Definition a48 : list trc := [
  [
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R23" [] (Val_Symbolic 37%Z) Mk_annot;
    Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R24" [] (Val_Symbolic 39%Z) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 27%Z)]) Mk_annot;
    Smt (DefineConst 42%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 11370:4 - 11380:5" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 42%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 43%Z (Val (Val_Symbolic 37%Z) Mk_annot)) Mk_annot;
    WriteReg "R23" [] (Val_Symbolic 43%Z) Mk_annot
  ];
  [
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R23" [] (Val_Symbolic 37%Z) Mk_annot;
    Smt (DeclareConst 39%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R24" [] (Val_Symbolic 39%Z) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 27%Z)]) Mk_annot;
    Smt (DefineConst 42%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 11370:4 - 11380:5" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 42%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 44%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 39%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R23" [] (Val_Symbolic 44%Z) Mk_annot
  ]
].
