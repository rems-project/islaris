From isla Require Import isla_lang.

Definition a8018c : list trc := [
  [
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    WriteReg "R1" [] (RegVal_Base (Val_Bits [BV{64%N} 0x5040%Z])) Mk_annot
  ]
].
