From isla Require Import opsem.

Definition ac : isla_trace :=
  AssumeReg "rv_enable_pmp" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  AssumeReg "rv_enable_misaligned_access" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  AssumeReg "rv_ram_base" [] (RegVal_Base (Val_Bits [BV{64%N} 0x80000000%Z])) Mk_annot :t:
  AssumeReg "rv_ram_size" [] (RegVal_Base (Val_Bits [BV{64%N} 0x4000000%Z])) Mk_annot :t:
  AssumeReg "rv_rom_base" [] (RegVal_Base (Val_Bits [BV{64%N} 0x1000%Z])) Mk_annot :t:
  AssumeReg "rv_rom_size" [] (RegVal_Base (Val_Bits [BV{64%N} 0x100%Z])) Mk_annot :t:
  AssumeReg "rv_clint_base" [] (RegVal_Base (Val_Bits [BV{64%N} 0x2000000%Z])) Mk_annot :t:
  AssumeReg "rv_clint_size" [] (RegVal_Base (Val_Bits [BV{64%N} 0xc0000%Z])) Mk_annot :t:
  AssumeReg "rv_htif_tohost" [] (RegVal_Base (Val_Bits [BV{64%N} 0x40001000%Z])) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "misa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 17%N 17%N) (AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 6%Z (Ty_Enum (Mk_enum_id 3%nat))) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 7%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 0%N) (AExp_Val (AVal_Var "x2" []) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{3%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop ((Bvcomp Bvuge)) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0x28%Z]) Mk_annot] Mk_annot) (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop ((Bvcomp Bvult)) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "x2" []) Mk_annot; AExp_Val (AVal_Bits [BV{64%N} 0x28%Z]) Mk_annot] Mk_annot) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot; AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 8%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 8%Z)) Mk_annot :t:
  Smt (DefineConst 9%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 8%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "x2" [] (RegVal_Base (Val_Symbolic 7%Z)) Mk_annot :t:
  Smt (DefineConst 21%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 7%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x28%Z]) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 6%Z)) Mk_annot :t:
  Smt (DeclareConst 35%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "satp" [] (RegVal_Base (Val_Symbolic 35%Z)) Mk_annot :t:
  Smt (DeclareConst 53%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "x9" [] (RegVal_Base (Val_Symbolic 53%Z)) Mk_annot :t:
  Smt (DefineConst 61%Z (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 21%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 67%Z (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 21%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 71%Z Ty_Bool) Mk_annot :t:
  WriteMem (RegVal_Base (Val_Symbolic 71%Z)) (RegVal_Base (Val_Enum ((Mk_enum_id 2%nat), Mk_enum_ctor 0%nat))) (RegVal_Base (Val_Symbolic 21%Z)) (RegVal_Base (Val_Symbolic 53%Z)) 8%N None Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 9%Z)) Mk_annot :t:
  tnil
.
