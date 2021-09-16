From isla Require Import isla_lang.

Definition aa9bf07e0 : list trc := [
  [
    Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
    Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
    Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop ((Bvcomp Bvugt)) (Val (Val_Symbolic 29%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x10%Z]) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits [BV{1%N} 0x1%Z]))]) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 29%Z)) Mk_annot;
    ReadReg "SCTLR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000002%Z])) Mk_annot;
    Smt (DefineConst 73%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 74%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R0" [] (RegVal_Base (Val_Symbolic 74%Z)) Mk_annot;
    Smt (DefineConst 75%Z (Val (Val_Symbolic 74%Z) Mk_annot)) Mk_annot;
    Smt (DeclareConst 76%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "R1" [] (RegVal_Base (Val_Symbolic 76%Z)) Mk_annot;
    Smt (DefineConst 77%Z (Val (Val_Symbolic 76%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 78%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "nRW"] (RegVal_Struct [("nRW", RegVal_Base (Val_Bits [BV{1%N} 0x0%Z]))]) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (RegVal_Base (Val_Bits [BV{4%N} 0x1%Z])) Mk_annot;
    Smt (DefineConst 83%Z (Binop (Eq) (Val (Val_Symbolic 78%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 83%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 83%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 78%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 78%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "SCR_EL3" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "TCR_EL2" [] (RegVal_Base (Val_Bits [BV{64%N} 0x0%Z])) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 83%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "PSTATE" [Field "D"] (RegVal_Struct [("D", RegVal_Base (Val_Symbolic 6%Z))]) Mk_annot;
    ReadReg "OSLSR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "OSDLR_EL1" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    ReadReg "EDSCR" [] (RegVal_Base (Val_Bits [BV{32%N} 0x0%Z])) Mk_annot;
    Smt (DeclareConst 1222%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "MPIDR_EL1" [] (RegVal_Base (Val_Symbolic 1222%Z)) Mk_annot;
    Smt (DeclareConst 1291%Z (Ty_BitVec 56%N)) Mk_annot;
    Smt (DefineConst 1304%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 78%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1305%Z Ty_Bool) Mk_annot;
    WriteMem (RegVal_Base (Val_Symbolic 1305%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 1304%Z)) (RegVal_Base (Val_Symbolic 75%Z)) 8%N None Mk_annot;
    Smt (DefineConst 1306%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 73%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DefineConst 1311%Z (Binop (Eq) (Val (Val_Symbolic 1306%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1306%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1311%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1311%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Binop (Eq) (Val (Val_Symbolic 1306%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 1306%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 1306%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 1311%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 2497%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 1306%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 2498%Z Ty_Bool) Mk_annot;
    WriteMem (RegVal_Base (Val_Symbolic 2498%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 2497%Z)) (RegVal_Base (Val_Symbolic 77%Z)) 8%N None Mk_annot;
    Smt (DefineConst 2499%Z (Val (Val_Symbolic 73%Z) Mk_annot)) Mk_annot;
    WriteReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 2499%Z)) Mk_annot
  ]
].
