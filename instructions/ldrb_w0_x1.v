From isla Require Import isla_lang.

Definition ldrb_w0_x1_trace : trc := [
  Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 28%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1683%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "R1" [] (Val_Symbolic 29%Z) Mk_annot;
  Smt (DefineConst 87%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DefineConst 91%Z (Binop (Eq) (Val (Val_Symbolic 87%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 87%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
  ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 91%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 91%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 87%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 87%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xffffffffffffffff%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
(*  ReadReg "__v84_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Symbolic 28%Z)]) Mk_annot;
  Smt (DefineConst 287%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 287%Z) Mk_annot) Mk_annot)) Mk_annot;
(*  ReadReg "__highest_el_aarch32" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 287%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 290%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 290%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 290%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v81_implemented" [] (Val_Bool true) Mk_annot;*)
  ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v83_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 87%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 902%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 902%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 902%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 905%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 905%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 905%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 934%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 934%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 934%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 937%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 937%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 937%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 976%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 976%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 976%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 91%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1184%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1184%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1184%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1187%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1187%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1187%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1226%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1226%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1226%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1229%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1229%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1229%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "D"] (Val_Struct [("D", Val_Symbolic 6%Z)]) Mk_annot;
  ReadReg "OSLSR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "OSDLR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "EDSCR" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  Smt (DefineConst 1264%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1264%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1264%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1267%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1267%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1267%Z) Mk_annot) Mk_annot)) Mk_annot;
(*  ReadReg "__v82_implemented" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__trickbox_enabled" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__CNTControlBase" [] (Val_Bits [BV{52%N} 0x0%Z]) Mk_annot;*)
  Smt (DeclareConst 1309%Z (Ty_BitVec 56%N)) Mk_annot;
(*  ReadReg "__defaultRAM" [] (Val_Symbolic 1309%Z) Mk_annot;*)
(*  ReadReg "__isla_monomorphize_reads" [] (Val_Bool false) Mk_annot;*)
  Smt (DefineConst 1318%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 87%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 1319%Z (Ty_BitVec 8%N)) Mk_annot;
  ReadMem (Val_Symbolic 1319%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 1318%Z) 1%N None Mk_annot;
  Smt (DefineConst 1321%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1321%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1321%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1325%Z (Manyop Concat [Val (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot; Manyop Concat [Val (Val_Bits [BV{24%N} 0x0%Z]) Mk_annot; Val (Val_Symbolic 1319%Z) Mk_annot] Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "R0" [] (Val_Symbolic 1325%Z) Mk_annot;
  Smt (DefineConst 1326%Z (Val (Val_Symbolic 87%Z) Mk_annot)) Mk_annot;
  WriteReg "R1" [] (Val_Symbolic 1326%Z) Mk_annot
].
