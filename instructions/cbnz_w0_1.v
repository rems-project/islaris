From isla Require Import isla_lang.

Definition cbnz_w0_1 : trc := [
  (* Cycle Mk_annot; *)
  (* ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot; *)
  (* WriteReg "SEE" [] (Val_I 1874%Z 128%Z) Mk_annot; *)
  (* WriteReg "__unconditional" [] (Val_Bool true) Mk_annot; *)
  (* ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot; *)
  Smt (DeclareConst 36%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R0" [] (Val_Symbolic 36%Z) Mk_annot;
  Smt (DefineConst 39%Z (Binop (Eq) (Binop (Eq) (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 36%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot) Mk_annot) (Val (Val_Bool false) Mk_annot) Mk_annot)) Mk_annot;
  (* Branch 0%Z "model/aarch64.sail 12148:4 - 12150:5" Mk_annot; *)
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 39%Z) Mk_annot) Mk_annot)) Mk_annot
].
