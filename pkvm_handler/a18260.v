From isla Require Import opsem.

Definition a18260 : isla_trace :=
  Barrier (RegVal_Base (Val_Enum ((Mk_enum_id 4%nat), Mk_enum_ctor 24%nat))) Mk_annot :t:
  Smt (DeclareConst 80%Z (Ty_BitVec 64%N)) Mk_annot :t:
  ReadReg "_PC" [] (RegVal_Base (Val_Symbolic 80%Z)) Mk_annot :t:
  Smt (DefineConst 81%Z (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 80%Z) Mk_annot; Val (Val_Bits (BV 64%N 0x4%Z)) Mk_annot] Mk_annot)) Mk_annot :t:
  WriteReg "_PC" [] (RegVal_Base (Val_Symbolic 81%Z)) Mk_annot :t:
  tnil
.
