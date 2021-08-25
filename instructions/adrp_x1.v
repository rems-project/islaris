From isla Require Import isla_lang.

Definition adrp_x1_trace : trc := [
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1394%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (DeclareConst 37%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "_PC" [] (Val_Symbolic 37%Z) Mk_annot;
  Smt (DefineConst 40%Z (Manyop (Bvmanyarith Bvadd) [Manyop (Bvmanyarith Bvor) [Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 37%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffff000%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "R1" [] (Val_Symbolic 40%Z) Mk_annot
].