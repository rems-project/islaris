From isla Require Import isla_lang.

Definition a34 : list trc := [
  [
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot
  ]
].
