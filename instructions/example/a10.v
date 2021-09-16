From isla Require Import isla_lang.

Definition a10 : list trc := [
  [
    WriteReg "R0" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot
  ]
].
