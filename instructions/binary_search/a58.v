From isla Require Import isla_lang.

Definition a58 : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R23" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot
  ]
].
