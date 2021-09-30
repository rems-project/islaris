From isla Require Import isla_lang.

Definition a7420 : list trc := [
  [
    AssumeReg "PSTATE" [Field "EL"] (RegVal_Base (Val_Bits [BV{2%N} 0x2%Z])) Mk_annot;
    AssumeReg "PSTATE" [Field "SP"] (RegVal_Base (Val_Bits [BV{1%N} 0x1%Z])) Mk_annot;
    ReadReg "PSTATE" [Field "SP"] (RegVal_Struct [("SP", RegVal_Base (Val_Bits [BV{1%N} 0x1%Z]))]) Mk_annot;
    ReadReg "PSTATE" [Field "EL"] (RegVal_Struct [("EL", RegVal_Base (Val_Bits [BV{2%N} 0x2%Z]))]) Mk_annot;
    Smt (DeclareConst 38%Z (Ty_BitVec 64%N)) Mk_annot;
    ReadReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 38%Z)) Mk_annot;
    Smt (DefineConst 61%Z (Manyop (Bvmanyarith Bvadd) [Unop (Extract 63%N 0%N) (Unop (ZeroExtend 64%N) (Val (Val_Symbolic 38%Z) Mk_annot) Mk_annot) Mk_annot; Val (Val_Bits [BV{64%N} 0x10%Z]) Mk_annot] Mk_annot)) Mk_annot;
    WriteReg "SP_EL2" [] (RegVal_Base (Val_Symbolic 61%Z)) Mk_annot
  ]
].
