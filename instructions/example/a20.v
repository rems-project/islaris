From isla Require Import isla_lang.

Definition a20 : list trc := [
  [
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot
  ]
].
