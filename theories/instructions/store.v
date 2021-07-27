From isla Require Import isla_lang.

Definition store_trace : trc := [
  Smt (DeclareConst 3%Z (Ty_BitVec 5%N)) Mk_annot;
  Smt (DeclareConst 4%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 5%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 6%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 7%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 8%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 9%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 10%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 11%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 12%Z (Ty_BitVec 2%N)) Mk_annot;
  Smt (DeclareConst 13%Z (Ty_BitVec 8%N)) Mk_annot;
  Smt (DeclareConst 14%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 16%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 17%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 18%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 19%Z (Ty_BitVec 4%N)) Mk_annot;
  Smt (DeclareConst 20%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 21%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 22%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 23%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 24%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 25%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 26%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 27%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 28%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
  (*ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;
  WriteReg "SEE" [] (Val_I 1277%Z 128%Z) Mk_annot;
  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;
  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "R1" [] (Val_Symbolic 29%Z) Mk_annot;
  Smt (DefineConst 90%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DeclareConst 91%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "R9" [] (Val_Symbolic 91%Z) Mk_annot;
  Smt (DefineConst 92%Z (Val (Val_Symbolic 91%Z) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("A", Val_Symbolic 17%Z); ("E", Val_Symbolic 21%Z); ("N", Val_Symbolic 7%Z); ("BTYPE", Val_Symbolic 12%Z); ("Z", Val_Symbolic 24%Z); ("EL", Val_Bits [BV{2%N} 0x2%Z]); ("IT", Val_Symbolic 13%Z); ("F", Val_Symbolic 6%Z); ("T", Val_Symbolic 18%Z); ("PAN", Val_Symbolic 25%Z); ("nRW", Val_Symbolic 28%Z); ("IL", Val_Symbolic 10%Z); ("GE", Val_Symbolic 19%Z); ("C", Val_Symbolic 27%Z); ("UAO", Val_Symbolic 26%Z); ("TCO", Val_Symbolic 14%Z); ("SS", Val_Symbolic 11%Z); ("M", Val_Symbolic 3%Z); ("SP", Val_Symbolic 5%Z); ("Q", Val_Symbolic 4%Z); ("SSBS", Val_Symbolic 8%Z); ("J", Val_Symbolic 20%Z); ("D", Val_Symbolic 22%Z); ("V", Val_Symbolic 23%Z); ("I", Val_Symbolic 16%Z); ("DIT", Val_Symbolic 9%Z)]) Mk_annot;
  (*ReadReg "__v84_implemented" [] (Val_Bool false) Mk_annot;*)
  ReadReg "PSTATE" [Field "nRW"] (Val_Struct [("A", Val_Symbolic 17%Z); ("E", Val_Symbolic 21%Z); ("N", Val_Symbolic 7%Z); ("BTYPE", Val_Symbolic 12%Z); ("Z", Val_Symbolic 24%Z); ("EL", Val_Bits [BV{2%N} 0x2%Z]); ("IT", Val_Symbolic 13%Z); ("F", Val_Symbolic 6%Z); ("T", Val_Symbolic 18%Z); ("PAN", Val_Symbolic 25%Z); ("nRW", Val_Symbolic 28%Z); ("IL", Val_Symbolic 10%Z); ("GE", Val_Symbolic 19%Z); ("C", Val_Symbolic 27%Z); ("UAO", Val_Symbolic 26%Z); ("TCO", Val_Symbolic 14%Z); ("SS", Val_Symbolic 11%Z); ("M", Val_Symbolic 3%Z); ("SP", Val_Symbolic 5%Z); ("Q", Val_Symbolic 4%Z); ("SSBS", Val_Symbolic 8%Z); ("J", Val_Symbolic 20%Z); ("D", Val_Symbolic 22%Z); ("V", Val_Symbolic 23%Z); ("I", Val_Symbolic 16%Z); ("DIT", Val_Symbolic 9%Z)]) Mk_annot;
  Smt (DefineConst 94%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL0" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL1" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL2" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 94%Z) Mk_annot) Mk_annot)) Mk_annot;
  (*ReadReg "__highest_el_aarch32" [] (Val_Bool false) Mk_annot;*)
  ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  Smt (DefineConst 99%Z (Binop (Eq) (Val (Val_Symbolic 90%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Unop (Not) (Val (Val_Symbolic 99%Z) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Binop (Eq) (Val (Val_Symbolic 90%Z) Mk_annot) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 90%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfffffffffffffff8%Z]) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 294%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 294%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 297%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 297%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  (*ReadReg "__v81_implemented" [] (Val_Bool true) Mk_annot;*)
  ReadReg "TCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
  (*ReadReg "__v83_implemented" [] (Val_Bool false) Mk_annot;*)
  Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 63%N 52%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{12%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 909%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 909%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 912%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 912%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 941%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 941%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 944%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 944%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 983%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 983%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1191%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1191%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1194%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1194%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1233%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1233%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1236%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1236%Z) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "D"] (Val_Struct [("A", Val_Symbolic 17%Z); ("E", Val_Symbolic 21%Z); ("N", Val_Symbolic 7%Z); ("BTYPE", Val_Symbolic 12%Z); ("Z", Val_Symbolic 24%Z); ("EL", Val_Bits [BV{2%N} 0x2%Z]); ("IT", Val_Symbolic 13%Z); ("F", Val_Symbolic 6%Z); ("T", Val_Symbolic 18%Z); ("PAN", Val_Symbolic 25%Z); ("nRW", Val_Symbolic 28%Z); ("IL", Val_Symbolic 10%Z); ("GE", Val_Symbolic 19%Z); ("C", Val_Symbolic 27%Z); ("UAO", Val_Symbolic 26%Z); ("TCO", Val_Symbolic 14%Z); ("SS", Val_Symbolic 11%Z); ("M", Val_Symbolic 3%Z); ("SP", Val_Symbolic 5%Z); ("Q", Val_Symbolic 4%Z); ("SSBS", Val_Symbolic 8%Z); ("J", Val_Symbolic 20%Z); ("D", Val_Symbolic 22%Z); ("V", Val_Symbolic 23%Z); ("I", Val_Symbolic 16%Z); ("DIT", Val_Symbolic 9%Z)]) Mk_annot;
  ReadReg "OSLSR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "OSDLR_EL1" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  ReadReg "EDSCR" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot;
  Smt (DeclareConst 1249%Z (Ty_BitVec 64%N)) Mk_annot;
  ReadReg "MPIDR_EL1" [] (Val_Symbolic 1249%Z) Mk_annot;
  Smt (DefineConst 1280%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1280%Z) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 1283%Z (Binop (Eq) (Val (Val_Symbolic 28%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop (Not) (Val (Val_Symbolic 1283%Z) Mk_annot) Mk_annot)) Mk_annot;
  (*ReadReg "__v82_implemented" [] (Val_Bool false) Mk_annot;
  ReadReg "__trickbox_enabled" [] (Val_Bool false) Mk_annot;
  ReadReg "__CNTControlBase" [] (Val_Bits [BV{52%N} 0x0%Z]) Mk_annot;*)
  Smt (DeclareConst 1323%Z (Ty_BitVec 56%N)) Mk_annot;
  (*ReadReg "__defaultRAM" [] (Val_Symbolic 1323%Z) Mk_annot;*)
  Smt (DefineConst 1336%Z (Unop (ZeroExtend 8%N) (Manyop Concat [Val (Val_Bits [BV{4%N} 0x0%Z]) Mk_annot; Unop (Extract 51%N 0%N) (Val (Val_Symbolic 90%Z) Mk_annot) Mk_annot] Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 1337%Z Ty_Bool) Mk_annot;
  WriteMem (Val_Symbolic 1337%Z) (Val_Enum ((Mk_enum_id 6%nat), Mk_enum_ctor 0%nat)) (Val_Symbolic 1336%Z) (Val_Symbolic 92%Z) 8%N None Mk_annot
].