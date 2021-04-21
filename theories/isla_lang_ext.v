Require Export isla.base isla.bitvector.
Require isla.isla_lang.

Definition var_name : Set := Z.

Definition register_name : Set := string.

Inductive enum_id : Type :=
| Mk_enum_id : nat -> enum_id.

Inductive enum_ctor : Type :=
| Mk_enum_ctor : nat -> enum_ctor.

Inductive annot : Type :=
| Mk_annot : annot.

Definition enum : Set := (enum_id*enum_ctor).

Inductive bvcomp : Set :=
 | Bvult : bvcomp
 | Bvslt : bvcomp
 | Bvule : bvcomp
 | Bvsle : bvcomp
 | Bvuge : bvcomp
 | Bvsge : bvcomp
 | Bvugt : bvcomp
 | Bvsgt : bvcomp.

Inductive bvarith : Set :=
 | Bvnand : bvarith
 | Bvnor : bvarith
 | Bvxnor : bvarith
 | Bvsub : bvarith
 | Bvudiv : bvarith
 | Bvudivi : bvarith
 | Bvsdiv : bvarith
 | Bvsdivi : bvarith
 | Bvurem : bvarith
 | Bvsrem : bvarith
 | Bvsmod : bvarith
 | Bvshl : bvarith
 | Bvlshr : bvarith
 | Bvashr : bvarith.

Inductive bvmanyarith : Set :=
 | Bvand : bvmanyarith
 | Bvor : bvmanyarith
 | Bvxor : bvmanyarith
 | Bvadd : bvmanyarith
 | Bvmul : bvmanyarith.

Inductive binop : Set :=
 | Eq : binop
 | Bvarith (bvarith5:bvarith)
 | Bvcomp (bvcomp5:bvcomp).

Inductive manyop : Set :=
 | And : manyop
 | Or : manyop
 | Bvmanyarith (bvmanyarith5:bvmanyarith)
 | Concat : manyop.

Inductive unop : Set :=
 | Not : unop
 | Bvnot : unop
 | Bvredand : unop
 | Bvredor : unop
 | Bvneg : unop
 | Extract (int5:Z) (int':Z)
 | ZeroExtend (int5:Z)
 | SignExtend (int5:Z).

Inductive valu : Set :=
 | Val_Symbolic (vvar5:var_name)
 | Val_Bool (bool5:bool)
 | Val_I (bvi5:Z) (int5:Z)
 | Val_Bits (bv5: bv)
 | Val_Enum (enum5:enum)
 | Val_String (str5:string)
 | Val_Unit : valu
 | Val_NamedUnit (name5:register_name)
 | Val_Vector (_:list valu)
 | Val_List (_:list valu)
 | Val_Struct (_:list (register_name * valu))
 | Val_Poison : valu.

Inductive ty : Set :=
 | Ty_Bool : ty
 | Ty_BitVec (int5:Z)
 | Ty_Enum (enum_ty5:enum_id)
 | Ty_Array (ty1:ty) (ty2:ty).

Inductive exp : Set :=
 | Val (vvar5:valu) (annot5:annot)
 | Unop (unop5:unop) (exp5:exp) (annot5:annot)
 | Binop (binop5:binop) (exp1:exp) (exp2:exp) (annot5:annot)
 | Manyop (manyop5:manyop) (_:list exp) (annot5:annot)
 | Ite (exp1:exp) (exp2:exp) (exp3:exp) (annot5:annot).

Inductive accessor : Set :=
 | Field (name5:register_name).

Definition valu_option : Set := option valu.

Inductive smt : Set :=
 | DeclareConst (vvar5:var_name) (ty5:ty)
 | DefineConst (vvar5:var_name) (exp5:exp)
 | Assert (exp5:exp)
 | DefineEnum (int5:Z).

Definition accessor_list : Set := list accessor.

Inductive event : Set :=
 | Smt (smt5:smt) (annot5:annot)
 | Branch (int5:Z) (str5:string) (annot5:annot) (*r Sail trace fork *)
 | ReadReg (name5:register_name) (accessor_list5:accessor_list) (valu5:valu) (annot5:annot) (*r read value `valu` from register `name` *)
 | WriteReg (name5:register_name) (accessor_list5:accessor_list) (valu5:valu) (annot5:annot) (*r write value `valu` to register `name` *)
 | ReadMem (valu5:valu) (rkind:valu) (addr:valu) (num_bytes:nat) (tag_value:valu_option) (annot5:annot) (*r read value `valu` from memory address `addr`, with read kind `rkind`, byte width `byte_width`, and `tag_value` is the optional capability tag *)
 | WriteMem (valu5:valu) (wkind:valu) (addr:valu) (data:valu) (num_bytes:nat) (tag_value:valu_option) (annot5:annot) (*r write value `valu` to memory address `addr`, with write kind `wkind`, byte width `byte_width`, `tag_value` is the optional capability tag, and success flag `vvar` *)
 | BranchAddress (addr:valu) (annot5:annot) (*r announce branch address `addr`, to induce ctrl dependency in the concurrency model *)
 | Barrier (bkind:valu) (annot5:annot) (*r memory barrier of kind `bkind` *)
 | CacheOp (ckind:valu) (addr:valu) (annot5:annot) (*r cache maintenance effect of kind `ckind`, at address `addr`, for data-cache clean etc. *)
 | MarkReg (name5:register_name) (str5:string) (annot5:annot) (*r instrumentation to tell concurrency model to ignore certain dependencies (TODO: support marking multiple registers). Currently the str is ignore-edge or ignore-write *)
 | Cycle (annot5:annot) (*r instruction boundary *)
 | Instr (opcode:valu) (annot5:annot) (*r records the instruction `opcode` that was fetched *)
 | Sleeping (vvar5:var_name) (annot5:annot) (*r Arm sleeping predicate *)
 | WakeRequest (annot5:annot) (*r Arm wake request *)
 | SleepRequest (annot5:annot) (*r Arm sleep request *).

Definition trc : Set := list event.


(*
TODO: finish the following
Section to_lang_ext.



  Fixpoint annot_to_ext (e : isla_lang.annot) : annot.
  Admitted.

  Fixpoint accessor_to_ext (e : isla_lang.accessor) : accessor.
  Admitted.

  Fixpoint valu_to_ext (e : isla_lang.valu) : valu.
  Admitted.

  Fixpoint ty_to_ext (e : isla_lang.ty) : ty.
  Admitted.

  Fixpoint enum_to_ext (e : isla_lang.enum) : enum.
  Admitted.

  Fixpoint exp_to_ext (e : isla_lang.exp) : exp :=
    match e with
    | isla_lang.Var vvar5 annot5 => Val (Val_Symbolic vvar5) (annot_to_ext annot5)
    | isla_lang.Bits bv5 annot5 => Val (Val_Bits bv5) (annot_to_ext annot5)
    | isla_lang.Bool bool5 annot5 => Val (Val_Bool bool5) (annot_to_ext annot5)
    | isla_lang.Enum enum5 annot5 => Val (Val_Enum (enum_to_ext enum5)) (annot_to_ext annot5)
    | isla_lang.Unop unop5 exp5 annot5 => Unop unop5 exp5 annot5
    | isla_lang.Binop binop5 exp1 exp2 annot5 => _
    | isla_lang.Manyop manyop5 x annot5 => _
    | isla_lang.Ite exp1 exp2 exp3 annot5 => _
    end.
  Admitted.

  Definition smt_to_ext (e : isla_lang.smt) : smt :=
    match e with
    | isla_lang.DeclareConst vvar5 ty5 => DeclareConst vvar5 (ty_to_ext ty5)
    | isla_lang.DefineConst vvar5 exp5 => DefineConst vvar5 (exp_to_ext exp5)
    | isla_lang.Assert exp5 => Assert (exp_to_ext exp5)
    | isla_lang.DefineEnum int5 => DefineEnum int5
    end.

  Admitted.

  Definition event_to_ext (e : isla_lang.event) : event :=
    match e with
    | isla_lang.Smt smt5 annot5 => Smt (smt_to_ext smt5) (annot_to_ext annot5)
    | isla_lang.Branch int5 str5 annot5 => Branch int5 str5 (annot_to_ext annot5)
    | isla_lang.ReadReg name5 accessor_list5 valu5 annot5 => ReadReg name5 (accessor_to_ext <$> accessor_list5) (valu_to_ext valu5) (annot_to_ext annot5)
    | isla_lang.WriteReg name5 accessor_list5 valu5 annot5 => WriteReg name5 (accessor_to_ext <$> accessor_list5) (valu_to_ext valu5) (annot_to_ext annot5)
    | isla_lang.ReadMem valu5 rkind addr num_bytes tag_value annot5 => ReadMem (valu_to_ext valu5) (valu_to_ext rkind) (valu_to_ext addr) num_bytes (valu_to_ext <$> tag_value) (annot_to_ext annot5)
    | isla_lang.WriteMem vvar5 wkind addr data num_bytes tag_value annot5 => WriteMem (Val_Symbolic vvar5) (valu_to_ext wkind) (valu_to_ext addr) (valu_to_ext data) num_bytes (valu_to_ext <$> tag_value) (annot_to_ext annot5)
    | isla_lang.BranchAddress addr annot5 => BranchAddress (valu_to_ext addr) (annot_to_ext annot5)
    | isla_lang.Barrier bkind annot5 => Barrier (valu_to_ext bkind) (annot_to_ext annot5)
    | isla_lang.CacheOp ckind addr annot5 => CacheOp (valu_to_ext ckind) (valu_to_ext addr) (annot_to_ext annot5)
    | isla_lang.MarkReg name5 str5 annot5 => MarkReg name5 str5 (annot_to_ext annot5)
    | isla_lang.Cycle annot5 => Cycle (annot_to_ext annot5)
    | isla_lang.Instr opcode annot5 => Instr (valu_to_ext opcode) (annot_to_ext annot5)
    | isla_lang.Sleeping vvar5 annot5 => Sleeping vvar5 (annot_to_ext annot5)
    | isla_lang.WakeRequest annot5 => WakeRequest (annot_to_ext annot5)
    | isla_lang.SleepRequest annot5 => SleepRequest (annot_to_ext annot5)
    end.
End to_lang_ext.
*)
