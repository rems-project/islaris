From isla Require Import isla_lang.

Definition ad2800003 : list trc := [
  [
    WriteReg "R3" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot
  ]
].
