From isla Require Import isla_lang.

Definition a8 : list trc := [
  [
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot;
    Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits [BV{64%N} 0x690%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R1" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot
  ]
].
