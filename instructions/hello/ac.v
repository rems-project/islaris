From isla Require Import isla_lang.

Definition ac : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R0" [] (RegVal_Base (Val_Bits [BV{64%N} 0x48%Z])) Mk_annot
  ]
].
