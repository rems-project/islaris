From isla Require Import isla_lang.

Definition str_x28_x27_trace : trc := [
  Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
(*  Cycle Mk_annot;*)
(*  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;*)
(*  WriteReg "SEE" [] (Val_I 1277%Z 128%Z) Mk_annot;*)
(*  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;*)
(*  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "R27" [] (Val_Symbolic 29%Z) Mk_annot;
  Smt (DefineConst 90%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DeclareConst 91%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R28" [] (Val_Symbolic 91%Z) Mk_annot;
  Smt (DefineConst 92%Z (Val (Val_Symbolic 91%Z) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
(*  ReadReg "__v84_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("nRW", Val_Bits [BV{1%N} 0x0%Z])]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
(*  ReadReg "__highest_el_aarch32" [] (Val_Bool false) Mk_annot;*)
  ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  Smt (DefineConst 97%Z (Binop (Eq) (Val (Val_Symbolic 90%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v81_implemented" [] (Val_Bool true) Mk_annot;*)
  ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
(*  ReadReg "__v83_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 97%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "D"] (Val_Struct [("D", Val_Symbolic 6%Z)]) Mk_annot;
  ReadReg "OSLSR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "OSDLR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "EDSCR" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  Smt (DeclareConst 1220%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "MPIDR_EL1" [] (Val_Symbolic 1220%Z) Mk_annot;
(*  ReadReg "__v82_implemented" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__trickbox_enabled" [] (Val_Bool false) Mk_annot;*)
(*  ReadReg "__CNTControlBase" [] (Val_Bits [BV{52%N} 0x0%Z]) Mk_annot;*)
  Smt (DeclareConst 1289%Z (Ty_BitVec 56%N)) Mk_annot;
(*  ReadReg "__defaultRAM" [] (Val_Symbolic 1289%Z) Mk_annot;*)
(*  ReadReg "__isla_monomorphize_writes" [] (Val_Bool false) Mk_annot;*)
  Smt (DefineConst 1302%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 1303%Z Ty_Bool) Mk_annot;
  WriteMem (Val_Symbolic 1303%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 1302%Z) (Val_Symbolic 92%Z) 8%N None Mk_annot
].
