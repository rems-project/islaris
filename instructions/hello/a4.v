From isla Require Import isla_lang.

Definition a4 : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x1000%Z])) Mk_annot
  ]
].
