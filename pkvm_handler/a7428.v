From isla Require Import isla_lang.

Definition a7428 : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R6" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot
  ]
].
