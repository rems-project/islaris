From isla Require Import isla_lang.

Definition a7404 : list trc := [
  [
    ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
    ReadReg "HCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
    ReadReg "SCTLR_EL1" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
    ReadReg "PSTATE" [Field "SP"] (Val_Struct [("SP", Val_Bits [BV{1%N} 0x1%Z])]) Mk_annot;
    ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
    ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot
  ]
].
