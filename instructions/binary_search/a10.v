From isla Require Import isla_lang.

Definition a10 : list trc := [
  [
    ReadReg "PSTATE" [Field "SP"] (Val_Struct [("SP", Val_Bits [BV{1%N} 0x1%Z])]) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "SP_EL2" [] (Val_Symbolic 38%Z) Mk_annot;
    Smt (DefineConst 59%Z (Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    WriteReg "R29" [] (Val_Symbolic 59%Z) Mk_annot
  ]
].
