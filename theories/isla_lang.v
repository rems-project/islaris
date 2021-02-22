(* isla-lang in Coq
 * Based on the Ott file from
 * https://github.com/rems-project/isla-lang/
 *
 * isla-lang is produced by isla:
 * https://github.com/rems-project/isla/
 *)

Require Import Arith Bool List String.


Definition PLACEHOLDER := nat (* TODO: get rid of this *).

Inductive annot : Type := (* TODO: is this useful? *)
| Mk_annot : annot.

Inductive enum_id : Type :=
| Mk_enum_id : nat -> enum_id.

Inductive enum_ctor : Type :=
| Mk_enum_ctor : nat -> enum_ctor.

Inductive field_name : Type :=
| Mk_field_name : nat -> field_name.

Inductive isla_var : Type :=
| Mk_isla_var : nat -> isla_var.

Definition isla_var_eqb (xv yv : isla_var) : bool :=
  match xv, yv with
  | Mk_isla_var x, Mk_isla_var y => Nat.eqb x y
  end.

Definition bits := list bool (* TODO: use a better representation? *).

Inductive i_type : Type :=
| I_64 : nat -> i_type
| I_128 : nat -> i_type
.

Record enum_member : Type := {
  enum_member_id: enum_id;
  enum_member_ctor: enum_ctor;
}.

Inductive valu : Set := 
| Val_Symbolic (x : isla_var)
| Val_Bool (b:bool)
| Val_I (i:i_type)
| Val_Bits (bs:bits)
| Val_Enum (em:enum_member)
| Val_String (str:unit (* TODO: we don't care for Coq purposes *) )
| Val_Unit : valu
| Val_NamedUnit (name5:PLACEHOLDER) (* TODO: where does this come from??? *)
| Val_Vector (vs:list valu)
| Val_List (vs:list valu)
| Val_Struct (ses:list (field_name * valu))
| Val_Poison : valu.

Fixpoint valu_eqb (v1 v2 : valu) : bool :=
    match v1, v2 with
    | Val_Bool b1, Val_Bool b2 => Bool.eqb b1 b2
    | _, _ => false (* TODO: other cases *)
    end.

Definition smt_var_map := isla_var -> option valu.

Fixpoint those_aux {A} (acc : option (list A)) (l : list (option A)) : option (list A) :=
match acc with
| None => None
| Some ys_rev =>
  match l with
  | nil => Some ys_rev
  | cons x xs =>
    match x with
    | None => None
    | Some y => those_aux (Some (cons y ys_rev)) xs
    end
  end
end.

Definition those {A} (l : list (option A)) : option (list A) :=
match those_aux (Some nil) l with
| None => None
| Some l => Some (List.rev l)
end.

(** the ISLA-lang type "valu" allows symbols, which are not values in the sense of an operational semantics *)
Fixpoint eval_valu (v : valu) (rho : smt_var_map) {struct v} : option valu :=
  match v with
  | Val_Symbolic x => rho x
  | Val_Bool b => Some (Val_Bool b)
  | Val_I i => Some (Val_I i)
  | Val_Bits bs => Some (Val_Bits bs)
  | Val_Enum em => Some (Val_Enum em)
  | Val_String s => Some (Val_String s)
  | Val_Unit => Some Val_Unit
  | Val_NamedUnit u => Some (Val_NamedUnit u)
  | Val_Vector vs =>
    match those (List.map (fun x => eval_valu x rho) vs) with
    | None => None
    | Some vs' => Some (Val_Vector vs')
    end
    | Val_List vs =>
    match those (List.map (fun x => eval_valu x rho) vs) with
    | None => None
    | Some vs' => Some (Val_List vs')
    end
  | Val_Struct s => Some (Val_Struct s)
  | Val_Poison => Some (Val_Poison)
  end.

Inductive unop : Set := 
| Not : unop
| Bvnot : unop
| Bvredand : unop
| Bvredor : unop
| Bvneg : unop
| Extract (int5:PLACEHOLDER) (int':PLACEHOLDER)
| ZeroExtend (int5:PLACEHOLDER)
| SignExtend (int5:PLACEHOLDER).

Definition eval_unop (u : unop) (v : valu) : option valu :=
match u, v with
| Not, Val_Bool b => Some (Val_Bool (negb b))
| Not, _ => None
| _, _ => (* TODO: other cases *) None
end.

Inductive bvmanyarith : Set := 
| Bvand : bvmanyarith
| Bvor : bvmanyarith
| Bvxor : bvmanyarith
| Bvadd : bvmanyarith
| Bvmul : bvmanyarith.

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

Inductive manyop : Set := 
| And : manyop
| Or : manyop
| Bvmanyarith (bvmanyarith5:bvmanyarith)
| Concat : manyop.

Inductive binop : Set := 
| Eq : binop
| Bvarith (bvarith5:bvarith)
| Bvcomp (bvcomp5:bvcomp).

Definition eval_binop (b : binop) (v1 v2 : valu) : option valu :=
match b, v1, v2 with
| Eq, Val_Bool b1, Val_Bool b2 => Some (Val_Bool (Bool.eqb b1 b2))
| _, _, _ => (* TODO: other cases *) None
end.

Inductive accessor : Set := 
 | Field (name5:PLACEHOLDER).

Inductive ty : Set := 
| Ty_Bool : ty
| Ty_BitVec (int5:PLACEHOLDER)
| Ty_Enum (enum_ty5:PLACEHOLDER).

Inductive exp : Set := 
| Var (x:isla_var) (an:annot)
| Bits (bs:bits) (ann:annot)
| Bool (b:bool) (ann:annot)
| Enum (em:enum_member) (ann:annot)
| Unop (uo:unop) (e:exp) (ann:annot)
| Binop (bo:binop) (e1:exp) (e2:exp) (ann:annot)
| Manyop (manyop5:manyop) (es:list exp) (ann:annot)
| Ite (exp1:exp) (exp2:exp) (exp3:exp) (ann:annot).

Definition option_bind {A B : Type} (f : A -> option B) (xo : option A) : option B :=
  match xo with
  | None => None
  | Some x => f x
  end.

Definition option_bind2 {A B C : Type} (f : A -> B -> option C) (xo : option A) (yo : option B) : option C :=
  match xo, yo with
  | None, _ => None
  | _, None => None
  | Some x, Some y => f x y
  end.

Fixpoint eval_exp (e : exp) (rho : smt_var_map) : option valu :=
  match e with
  | Var x _ => rho x
  | Bits n _ => Some (Val_Bits n)
  | Bool b _ => Some (Val_Bool b)
  | Enum em _ => Some (Val_Enum em)
  | Unop uo e' _ =>
    option_bind (eval_unop uo) (eval_exp e' rho)
  | Binop uo e1 e2 _ =>
    option_bind2 (eval_binop uo) (eval_exp e1 rho) (eval_exp e2 rho)
  | Manyop _ _ _ => None (* TODO *)
  | Ite e1 e2 e3 _ =>
    match eval_exp e1 rho with
    | Some (Val_Bool true) => eval_exp e2 rho
    | Some (Val_Bool false) => eval_exp e3 rho
    | _ => None
    end
  end.

(* huh? *)
Inductive accessor_list : Set := 
| ISLA_Nil : accessor_list
| ISLA_Cons (_:list accessor).

Inductive smt : Set := 
| DeclareConst (vvar5 : isla_var) (ty5 : ty)
| DefineConst (vvar5 : isla_var) (exp5 : exp)
| Assert (exp5:exp)
| DefineEnum (int5:PLACEHOLDER) (* TODO: ??? *).

Inductive register : Type :=
| Mk_register : string -> register.

Definition register_eqb (xv yv : register) : bool :=
  match xv, yv with
  | Mk_register x, Mk_register y => String.eqb x y
  end.

Inductive event : Set := 
| Smt (smt:smt) (ann:annot)
| Fork (n:nat) (sail_loc:unit) (ann:annot) (** for documentation, TODO: this is called `Branch` in the text output of sail; probably should be changed ??? *)
| ReadReg (reg:register) (al:accessor_list) (val:valu) (ann:annot)
| WriteReg (reg:register) (al:accessor_list) (val:valu) (ann:annot)
| ReadMem (rkind:valu) (addr:valu) (val:valu) (num_bytes:nat) (tag_value:option valu) (ann:annot)
| WriteMem (retval:valu) (wkind:valu) (addr:valu) (val:valu) (num_bytes:nat) (tag_value:option valu) (ann:annot)
| BranchAddress (addr:valu) (ann:annot) (** announce a branch, to induce a `ctrl` dependency in the concurrency memory model *)
| Barrier (bkind:valu) (ann:annot)
| CacheOp (ckind:valu) (valu':valu) (ann:annot) (** for data cache clean, instruction cache clean, etc. *)
| MarkReg (reg:register) (str:unit) (ann:annot) (** to mark a register as not inducing a dependency, in the concurrency memory model *)
| Cycle (ann:annot) (** separates different instructions *)
| Instr (opcode:valu) (ann:annot) (** records what instruction was fetched *)
(* TODO: the below sleep-related instructions don't matter too much for now *)
| Sleeping (v:valu) (ann:annot)
| WakeRequest (ann:annot)
| SleepRequest (ann:annot).

Inductive trc : Set := 
| Trace (es:list event).

Inductive write_kind : Type :=
| Mk_write_kind : enum_ctor -> write_kind
.

Inductive proper_label : Type :=
| PLAB_read_reg (r : register) (v : valu) : proper_label
| PLAB_write_mem (kd : write_kind) (addr : valu) (val : valu) (ret : valu) (num_bytes : nat) (tag_value : bool) : proper_label
(* TODO: other cases *).

Inductive label : Type :=
| LAB_tau : label
| LAB_non_tau : proper_label -> label
.

Inductive event_step : event -> smt_var_map -> label -> smt_var_map -> Prop :=
| es_declare_const rho x ty v ann :
  rho x = None ->
  event_step (Smt (DeclareConst x ty) ann) rho LAB_tau (fun y => if isla_var_eqb x y then Some v else rho y)
| es_assert rho e ann :
  eval_exp e rho = Some (Val_Bool true) ->
  event_step (Smt (Assert e) ann) rho LAB_tau rho
| es_read_reg rho r al v ann :
  event_step (ReadReg r al v ann) rho (LAB_non_tau (PLAB_read_reg r v)) rho
| es_write_mem rho ret_sym x_sym al v_sym wkd_sym num_bytes tag_value_sym x v ret wkd tag_value :
  (* TODO: What to do with tag_value? *)
  eval_valu x_sym rho = Some x ->
  eval_valu v_sym rho = Some v ->
  eval_valu ret_sym rho = Some ret ->
  eval_valu wkd_sym rho = Some (Val_Enum wkd) ->
  event_step (WriteMem ret_sym wkd_sym x_sym v_sym num_bytes tag_value_sym al) rho (LAB_non_tau (PLAB_write_mem (Mk_write_kind wkd.(enum_member_ctor)) x v ret num_bytes tag_value)) rho
(* TODO: other cases *)
.

Record sequential_state := {
  seqst_reg_map : register -> valu;
  seqst_mem_map : valu -> option valu;
}.

Inductive sequential_state_step : sequential_state -> proper_label -> sequential_state -> Prop :=
| seqststep_read_reg seqst r v :
  seqst.(seqst_reg_map) r = v ->
  sequential_state_step seqst (PLAB_read_reg r v) seqst
| seqststep_write_mem seqst ret wkd x v num_bytes tv :
  (* TODO: this assumes every write is of one byte *)
  sequential_state_step seqst (PLAB_write_mem ret wkd x v num_bytes tv)
    {| seqst_reg_map := seqst.(seqst_reg_map);
       seqst_mem_map := fun y => if valu_eqb x y then Some v else seqst.(seqst_mem_map) y |}
(* TODO: other cases *).

Record sequential_system_state := {
  seqsysst_smt_var_map : smt_var_map;
  seqsysst_seq_st : sequential_state;
}.

Inductive sequential_system_head_step :
  event -> sequential_system_state ->
  sequential_system_state ->
  Prop :=
| seq_sys_step_tau e seqsysst rho rho' :
  event_step e rho LAB_tau rho' ->
  sequential_system_head_step
    e
    {| seqsysst_smt_var_map := rho; seqsysst_seq_st := seqsysst |}
    {| seqsysst_smt_var_map := rho'; seqsysst_seq_st := seqsysst |}
| seq_sys_step_non_tau e rho seqsysst plab rho' seqsysst' :
  event_step e rho (LAB_non_tau plab) rho' ->
  sequential_state_step seqsysst plab seqsysst' ->
  sequential_system_head_step
    e
    {| seqsysst_smt_var_map := rho; seqsysst_seq_st := seqsysst |}
    {| seqsysst_smt_var_map := rho'; seqsysst_seq_st := seqsysst' |}
.

Inductive trace_system_step : trc -> sequential_system_state -> trc -> sequential_system_state -> Prop :=
| tss_cons e es sys sys' :
  sequential_system_head_step e sys sys' ->
  trace_system_step (Trace (e :: es)) sys (Trace es) sys'
.

Definition instruction := list trc.

Inductive trace_step : trc -> smt_var_map -> label -> trc -> smt_var_map -> Prop :=
| ts_cons e es rho lab rho' :
  event_step e rho lab rho' ->
  trace_step (Trace (e :: es)) rho lab (Trace es) rho'
.

Definition rho0 : smt_var_map := (fun _ => None).

Definition related_label (l1 l2 : proper_label) : Prop :=
  match l1, l2 with
  | PLAB_read_reg r1 v1, PLAB_read_reg r2 v2 =>
    r1 = r2
  | PLAB_write_mem kd1 x1 v1 ret1 num_bytes1 tag_value1,
    PLAB_write_mem kd2 x2 v2 ret2 num_bytes2 tag_value2 =>
    (* TODO: tag_value? *)
    kd1 = kd2 /\ num_bytes1 = num_bytes2 /\ x1 = x2
  | _, _ => False
  end.

Inductive trace_any_steps : trc -> smt_var_map -> trc -> smt_var_map -> Prop :=
| trace_any_steps_refl trc rho :
  trace_any_steps trc rho trc rho
| trace_any_steps_step trc rho lab trc' rho' trc'' rho'' :
  trace_step trc rho lab trc' rho' ->
  trace_any_steps trc' rho' trc'' rho'' ->
  trace_any_steps trc rho trc'' rho''
.

(* A set of traces counts as a proper instruction,
  when it never gets stuck: there is always another trace
  that can read another value *)
Definition instruction_is_live (i : instruction) : Prop :=
    forall (tr : trc) tr1 tr' rho1 rho' lab,
    (exists trs1 trs2, i = trs1 ++ (tr :: trs2)) ->
    trace_any_steps tr rho0 tr1 rho1 ->
    trace_step tr1 rho1 (LAB_non_tau lab) tr' rho' ->
    forall lab',
    related_label lab lab' ->
    exists tr'' rho'',
    trace_step tr rho1 (LAB_non_tau lab') tr'' rho''
.

(* TODO: chain multiple instructions *)