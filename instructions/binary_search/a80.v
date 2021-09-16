From isla Require Import isla_lang.

Definition a80 : list trc := [
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    Smt (DefineConst 38%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 11344:19 - 11344:52" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 27%Z)]) Mk_annot;
    Smt (DefineConst 39%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 1%Z "model/aarch64.sail 11370:4 - 11380:5" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 39%Z) Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot
  ];
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    Smt (DefineConst 38%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 11344:19 - 11344:52" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 38%Z) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "Z"] (Val_Struct [("Z", Val_Symbolic 27%Z)]) Mk_annot;
    Smt (DefineConst 39%Z (Binop (Eq) (Val (Val_Symbolic 27%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 1%Z "model/aarch64.sail 11370:4 - 11380:5" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot
  ];
  [
    Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
    ReadReg "PSTATE" [Field "C"] (Val_Struct [("C", Val_Symbolic 5%Z)]) Mk_annot;
    Smt (DefineConst 38%Z (Binop (Eq) (Val (Val_Symbolic 5%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/aarch64.sail 11344:19 - 11344:52" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot)) Mk_annot;
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot
  ]
].
