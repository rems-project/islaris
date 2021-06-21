From isla Require Import isla_lang.

Definition trace : trc := [
  Smt (DeclareConst 23%Z (Ty_BitVec 1%N)) Mk_annot;
  Smt (DeclareConst 29%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 29%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DeclareConst 30%Z (Ty_BitVec 64%N)) Mk_annot;
  Smt (Assert (Binop (Eq) (Manyop (Bvmanyarith Bvand) [Val (Val_Symbolic 30%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0xfff0000000000007%Z]) Mk_annot] Mk_annot) (Val (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot) Mk_annot)) Mk_annot;
  Cycle Mk_annot;
  ReadReg "SEE" [] (Val_I (-1)%Z 128%Z) Mk_annot;
  WriteReg "SEE" [] (Val_I 1800%Z 128%Z) Mk_annot;
  WriteReg "__unconditional" [] (Val_Bool true) Mk_annot;
  ReadReg "__v85_implemented" [] (Val_Bool false) Mk_annot;
  ReadReg "PSTATE" [Field "EL"] (Val_Struct [("EL", Val_Bits [BV{2%N} 0x2%Z])]) Mk_annot;
  ReadReg "HCR_EL2" [] (Val_Bits [BV{64%N} 0x0%Z]) Mk_annot;
  ReadReg "SCTLR_EL1" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  ReadReg "PSTATE" [Field "SP"] (Val_Struct [("SP", Val_Symbolic 23%Z)]) Mk_annot;
  ReadReg "SCTLR_EL2" [] (Val_Bits [BV{64%N} 0x4000002%Z]) Mk_annot;
  ReadReg "CFG_ID_AA64PFR0_EL1_EL3" [] (Val_Bits [BV{4%N} 0x1%Z]) Mk_annot;
  ReadReg "SCR_EL3" [] (Val_Bits [BV{32%N} 0x0%Z]) Mk_annot
].
