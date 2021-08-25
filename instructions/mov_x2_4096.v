From isla Require Import isla_lang.

Definition mov_x2_4096_trace : trc := [
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1486%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  WriteReg "R2" [] (Val_Bits [BV{64%N} 0x1000%Z]) Mk_annot
].
