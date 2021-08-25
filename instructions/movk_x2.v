From isla Require Import isla_lang.

Definition movk_x2_trace : trc := [
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1169%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (DeclareConst 44%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R2" [] (Val_Symbolic 44%Z) Mk_annot;
  Smt (DefineConst 47%Z (Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 44%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffff0000ffff%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x101f0000%Z]) Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "R2" [] (Val_Symbolic 47%Z) Mk_annot
].
