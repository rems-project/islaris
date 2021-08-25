From isla Require Import isla_lang.

Definition add_x1_x1_0x690_trace : trc := [
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1066%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R1" [] (Val_Symbolic 38%Z) Mk_annot;
  Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits [BV{64%N} 0x690%Z]) Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "R1" [] (Val_Symbolic 61%Z) Mk_annot
].
