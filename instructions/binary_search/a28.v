From isla Require Import isla_lang.

Definition a28 : list trc := [
  [
    WriteReg "R23" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot
  ]
].
