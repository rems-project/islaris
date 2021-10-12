From isla Require Import isla_lang.

Definition a8 : list trc := [
  [
    Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot;
    Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "zmisa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot;
    Smt (Assert (Binop (Eq) (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot;
    Smt (DefineConst 2%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x10" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot;
    Smt (DeclareConst 15%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x11" [] (RegVal_Base (Val_Symbolic 15%Z)) Mk_annot;
    Smt (DefineConst 16%Z (Binop (Eq) (Val (Val_Symbolic 14%Z) Mk_annot) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot)) Mk_annot;
    Branch 0%Z "model/riscv_insts_base.sail 186:2 - 204:23" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 16%Z) Mk_annot) Mk_annot)) Mk_annot;
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 2%Z)) Mk_annot
  ];
  [
    Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot;
    Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "zmisa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot;
    Smt (Assert (Binop (Eq) (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot;
    Smt (DefineConst 2%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x10" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot;
    Smt (DeclareConst 15%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x11" [] (RegVal_Base (Val_Symbolic 15%Z)) Mk_annot;
    Smt (DefineConst 16%Z (Binop (Eq) (Val (Val_Symbolic 14%Z) Mk_annot) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 17%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Branch 0%Z "model/riscv_insts_base.sail 186:2 - 204:23" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 16%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 18%Z (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 17%Z) Mk_annot) (Val (Val_Bits [BV{64%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 20%Z (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 18%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Branch 1%Z "model/prelude.sail 224:25 - 227:1" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 20%Z) Mk_annot)) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Val (Val_Symbolic 18%Z) Mk_annot) (Val (Val_Bits [BV{1%N} 0x0%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    BranchAddress (RegVal_Base (Val_Symbolic 17%Z)) Mk_annot;
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 17%Z)) Mk_annot
  ];
  [
    Smt (DeclareConst 0%Z (Ty_BitVec 64%N)) Mk_annot;
    Assume (AExp_Binop (Eq) (AExp_Unop (Extract 2%N 2%N) (AExp_Val (AVal_Var "zmisa" [Field "bits"]) Mk_annot) Mk_annot) (AExp_Val (AVal_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot;
    Smt (Assert (Binop (Eq) (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DeclareConst 1%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "PC" [] (RegVal_Base (Val_Symbolic 1%Z)) Mk_annot;
    Smt (DefineConst 2%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x4%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Smt (DeclareConst 14%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x10" [] (RegVal_Base (Val_Symbolic 14%Z)) Mk_annot;
    Smt (DeclareConst 15%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "x11" [] (RegVal_Base (Val_Symbolic 15%Z)) Mk_annot;
    Smt (DefineConst 16%Z (Binop (Eq) (Val (Val_Symbolic 14%Z) Mk_annot) (Val (Val_Symbolic 15%Z) Mk_annot) Mk_annot)) Mk_annot;
    Smt (DefineConst 17%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 1%Z) Mk_annot; Val (Val_Bits [BV{64%N} 0x8%Z]) Mk_annot] Mk_annot)) Mk_annot;
    Branch 0%Z "model/riscv_insts_base.sail 186:2 - 204:23" Mk_annot;
    Smt (Assert (Val (Val_Symbolic 16%Z) Mk_annot)) Mk_annot;
    Smt (DefineConst 20%Z (Unop (Not) (Binop (Eq) (Unop (Extract 0%N 0%N) (Binop ((Bvarith Bvlshr)) (Val (Val_Symbolic 17%Z) Mk_annot) (Unop (Extract 63%N 0%N) (Val (Val_Bits [BV{128%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    Branch 1%Z "model/prelude.sail 224:25 - 227:1" Mk_annot;
    Smt (Assert (Unop (Not) (Val (Val_Symbolic 20%Z) Mk_annot) Mk_annot)) Mk_annot;
    ReadReg "misa" [] (RegVal_Struct [("bits", RegVal_Base (Val_Symbolic 0%Z))]) Mk_annot;
    Smt (Assert (Unop (Not) (Unop (Not) (Binop (Eq) (Unop (Extract 2%N 2%N) (Val (Val_Symbolic 0%Z) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1%N} 0x1%Z]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
    BranchAddress (RegVal_Base (Val_Symbolic 17%Z)) Mk_annot;
    WriteReg "PC" [] (RegVal_Base (Val_Symbolic 17%Z)) Mk_annot
  ]
].
