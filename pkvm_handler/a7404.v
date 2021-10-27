From isla Require Import isla_lang.

Definition a7404 : list trc := [
  [
    AssumeReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits [BV{1%N} 0x1%Z])) Mk_annot;
    AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    AssumeReg "SCTLR_EL1" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot;
    ReadReg "SCTLR_EL1" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    ReadReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits [BV{1%N} 0x1%Z]))]) Mk_annot;
    ReadReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    Smt (DeclareConst 69%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "CPTR_EL2" [] (RegVal_Base (Val_Symbolic 69%Z)) Mk_annot;
    Smt (DeclareConst 71%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "CPTR_EL3" [] (RegVal_Base (Val_Symbolic 71%Z)) Mk_annot;
    Smt (DeclareConst 76%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "CPACR_EL1" [] (RegVal_Base (Val_Symbolic 76%Z)) Mk_annot;
    Smt (DeclareConst 84%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "CNTHCTL_EL2" [] (RegVal_Base (Val_Symbolic 84%Z)) Mk_annot;
    Smt (DeclareConst 87%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "MDCR_EL2" [] (RegVal_Base (Val_Symbolic 87%Z)) Mk_annot;
    Smt (DeclareConst 90%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "ICC_SRE_EL2" [] (RegVal_Base (Val_Symbolic 90%Z)) Mk_annot;
    ReadReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 95%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "CNTKCTL_EL1" [] (RegVal_Base (Val_Symbolic 95%Z)) Mk_annot;
    Smt (DeclareConst 104%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPAM2_EL2" [] (RegVal_Base (Val_Symbolic 104%Z)) Mk_annot;
    Smt (DeclareConst 107%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "MDCR_EL3" [] (RegVal_Base (Val_Symbolic 107%Z)) Mk_annot;
    Smt (DeclareConst 128%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "ICH_HCR_EL2" [] (RegVal_Base (Val_Symbolic 128%Z)) Mk_annot;
    Smt (DeclareConst 141%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "ICC_SRE_EL1_NS" [] (RegVal_Base (Val_Symbolic 141%Z)) Mk_annot;
    Smt (DeclareConst 146%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPAMIDR_EL1" [] (RegVal_Base (Val_Symbolic 146%Z)) Mk_annot;
    Smt (DeclareConst 160%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "PMUSERENR_EL0" [] (RegVal_Base (Val_Symbolic 160%Z)) Mk_annot;
    Smt (DeclareConst 167%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPAM3_EL3" [] (RegVal_Base (Val_Symbolic 167%Z)) Mk_annot;
    Smt (DeclareConst 170%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "ICC_SRE_EL3" [] (RegVal_Base (Val_Symbolic 170%Z)) Mk_annot;
    Smt (DeclareConst 177%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "MPAMHCR_EL2" [] (RegVal_Base (Val_Symbolic 177%Z)) Mk_annot;
    Smt (DeclareConst 194%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "HSTR_EL2" [] (RegVal_Base (Val_Symbolic 194%Z)) Mk_annot;
    ReadReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "MDSCR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 216%Z (Ty_BitVec 32%N)) Mk_annot;
    ReadReg "ESR_EL2" [] (RegVal_Base (Val_Symbolic 216%Z)) Mk_annot;
    Smt (DefineConst 218%Z (Manyop Concat [Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 216%Z) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "R0" [] (RegVal_Base (Val_Symbolic 218%Z)) Mk_annot;
    Smt (DeclareConst 219%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 219%Z)) Mk_annot;
    Smt (DefineConst 220%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 219%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 220%Z)) Mk_annot
  ]
].
