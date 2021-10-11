From isla Require Import isla_lang.

Definition a80168 : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x5054%Z])) Mk_annot
  ]
].
