From isla Require Import isla_lang.

Definition a28 : list trc := [
  [
    AssumeReg "__highest_el_aarch32" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v84_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v83_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v81_implemented" [] (RegVal_Base (Val_Bool true)) Mk_annot;
    AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot;
    AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    Smt (DeclareConst 47%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 47%Z)) Mk_annot;
    Smt (DefineConst 49%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 47%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R30" [] (RegVal_Base (Val_Symbolic 49%Z)) Mk_annot;
    Smt (DefineConst 50%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 47%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xc%Z]) Mk_annot] Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    Smt (DefineConst 51%Z (Val (Val_Symbolic 50%Z) Mk_annot)) Mk_annot;
    BranchAddress (RegVal_Base (Val_Symbolic 51%Z)) Mk_annot;
    Smt (DefineConst 52%Z (Val (Val_Symbolic 50%Z) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 52%Z)) Mk_annot;
    WriteReg "__PC_changed" [] (RegVal_Base (Val_Bool true)) Mk_annot
  ]
].
