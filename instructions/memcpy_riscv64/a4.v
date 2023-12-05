From isla Require Import opsem.

Definition a4 : isla_trace :=
  AssumeReg "rv_enable_pmp" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  AssumeReg "rv_enable_misaligned_access" [] (RegVal_Base (Val_Bool false)) Mk_annot :t:
  AssumeReg "rv_ram_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x80000000%Z))) Mk_annot :t:
  AssumeReg "rv_ram_size" [] (RegVal_Base (Val_Bits (BV 64%N 0x4000000%Z))) Mk_annot :t:
  AssumeReg "rv_rom_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x1000%Z))) Mk_annot :t:
  AssumeReg "rv_rom_size" [] (RegVal_Base (Val_Bits (BV 64%N 0x100%Z))) Mk_annot :t:
  AssumeReg "rv_clint_base" [] (RegVal_Base (Val_Bits (BV 64%N 0x2000000%Z))) Mk_annot :t:
  AssumeReg "rv_clint_size" [] (RegVal_Base (Val_Bits (BV 64%N 0xc0000%Z))) Mk_annot :t:
  AssumeReg "rv_htif_tohost" [] (RegVal_Base (Val_Bits (BV 64%N 0x40001000%Z))) Mk_annot :t:
  Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "misa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits (BV 1%N 0x1%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Manyop (Bvmanyarith Bvand) [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot; AExp_Val (AVal_Bits (BV 64%N 0x20000%Z)) Mk_annot] Mk_annot) (AExp_Val (AVal_Bits (BV 64%N 0x0%Z)) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 2%Z (Ty_Enum "Privilege")) Mk_annot :t:
  Assume (AExp_Binop (Eq) (AExp_Val (AVal_Var "cur_privilege" []) Mk_annot) (AExp_Val (AVal_Var "Machine" []) Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 3%Z (Ty_BitVec 64%N)) Mk_annot :t:
  Assume (AExp_Binop ((Bvcomp Bvuge)) (AExp_Val (AVal_Var "x11" []) Mk_annot) (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot) Mk_annot :t:
  Assume (AExp_Binop ((Bvcomp Bvult)) (AExp_Val (AVal_Var "x11" []) Mk_annot) (AExp_Manyop (Bvmanyarith Bvadd) [AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot; AExp_Val (AVal_Var "rv_ram_size" []) Mk_annot] Mk_annot) Mk_annot) Mk_annot :t:
  Smt (DeclareConst 4%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "PC" [] (RegVal_Base (Val_Symbolic 4%Z)) Mk_annot :t:
  Smt (DefineConst 5%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 4%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "x11" [] (RegVal_Base (Val_Symbolic 3%Z)) Mk_annot :t:
  Smt (DefineConst 6%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x0%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  ReadReg "mstatus" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 1%Z))]) Mk_annot :t:
  ReadReg "cur_privilege" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot :t:
  Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "satp" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot :t:
  Smt (DefineConst 21%Z (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 6%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DefineConst 27%Z (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 6%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  Smt (DeclareConst 31%Z (Ty_BitVec 8%N)) Mk_annot :t:
  ReadMem (RegVal_Base (Val_Symbolic 31%Z)) (RegVal_Poison) (RegVal_Base (Val_Symbolic 6%Z)) 1%N None Mk_annot :t:
  Smt (DefineConst 32%Z (Unop (SignExtend 56%N) (Val (Val_Symbolic 31%Z) Mk_annot) Mk_annot)) Mk_annot :t:
  WriteReg "x13" [] (RegVal_Base (Val_Symbolic 32%Z)) Mk_annot :t:
  WriteReg "PC" [] (RegVal_Base (Val_Symbolic 5%Z)) Mk_annot :t:
  tnil
.
