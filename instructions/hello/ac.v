From isla Require Import isla_lang.

Definition ac : list trc := [
  [
    WriteReg "R0" [] (Val_Bits [BV{64%N} 0x48%Z]) Mk_annot
  ]
].
