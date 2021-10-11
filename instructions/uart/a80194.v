From isla Require Import isla_lang.

Definition a80194 : list trc := [
  [
    AssumeReg "__isla_monomorphize_writes" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__highest_el_aarch32" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__CNTControlBase" [] (RegVal_Base (Val_Bits [BV{52%N} 0x0%Z])) Mk_annot;
    AssumeReg "__v85_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v84_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v83_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v82_implemented" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "__v81_implemented" [] (RegVal_Base (Val_Bool true)) Mk_annot;
    AssumeReg "__trickbox_enabled" [] (RegVal_Base (Val_Bool false)) Mk_annot;
    AssumeReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    AssumeReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    AssumeReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    AssumeReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    AssumeReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
    AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "nRW"] (RegVal_Base (Val_Bits [BV{1%N} 0x0%Z])) Mk_annot;
    AssumeReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    AssumeReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
    Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "R1" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0xfff0000000000003%Z]) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot;
    Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000003%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot;
    Smt (DefineConst 90%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 91%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 91%Z)) Mk_annot;
    Smt (DefineConst 92%Z (Unop (Extract 31%N 0%N) (Val (Val_Symbolic 91%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    Smt (DefineConst 97%Z (Binop (Eq) (Val (Val_Symbolic 90%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffffc%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 90%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffffc%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x401%Z])) Mk_annot;
    ReadReg "HCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot;
    ReadReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 1259%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 1259%Z)) Mk_annot;
    Smt (DeclareConst 1328%Z (Ty_BitVec 56%N)) Mk_annot;
    Smt (DefineConst 1341%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1342%Z Ty_Bool) Mk_annot;
    WriteMem (RegVal_Base (Val_Symbolic 1342%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 1341%Z)) (RegVal_Base (Val_Symbolic 92%Z)) 4%N None Mk_annot
  ]
].
