Require Export isla.isla_lang_ext.

Fixpoint subst_valu (n : var_name) (z : valu) (v : valu) {struct v} : valu :=
  match v with
  | Val_Symbolic x => if bool_decide (n = x) then z else Val_Symbolic x
  | Val_Bool b => Val_Bool b
  | Val_I x i => Val_I x i
  | Val_Bits bs => Val_Bits bs
  | Val_Enum em => Val_Enum em
  | Val_String s => Val_String s
  | Val_Unit => Val_Unit
  | Val_NamedUnit u => Val_NamedUnit u
  | Val_Vector vs => Val_Vector (subst_valu n z <$> vs)
  | Val_List vs => Val_List (subst_valu n z <$> vs)
  | Val_Struct s => Val_Struct s
  | Val_Poison => Val_Poison
  end.

Fixpoint subst_exp (n : var_name) (v : valu) (e : exp) {struct e} : exp.
(* TODO: How to fill this in? exp does not have a val constructor *)
Admitted.

Definition subst_smt (n : var_name) (v : valu) (s : smt) : smt :=
  match s with
  (* TODO: What to do on name clash? Return option? *)
  | DeclareConst _ _ => s
  | DefineConst r e => DefineConst r (subst_exp n v e)
  | Assert e => Assert (subst_exp n v e)
  | DefineEnum _ => s
  end.

Definition subst_event (n : var_name) (v : valu) (e : event) : event :=
  match e with
  | Smt s ann => Smt (subst_smt n v s) ann

  | Branch _ _ _ | BranchAddress _ _ | Barrier _ _ | CacheOp _ _ _
  | MarkReg _ _ _ | Cycle _ | Instr _ _ | Sleeping _ _ | WakeRequest _ | SleepRequest _ => e

  | ReadReg r al vr ann => ReadReg r al (subst_valu n v vr) ann
  | WriteReg r al vr ann => WriteReg r al (subst_valu n v vr) ann
  | ReadMem vr rkind addr len tag_value ann => ReadMem (subst_valu n v vr) (subst_valu n v rkind) (subst_valu n v addr) len (subst_valu n v <$> tag_value) ann
  (* TODO: handle the following. How to subsitute the var? *)
  | WriteMem vvar5 wkind addr data nat5 tag_value ann => e
  end.

Definition eval_unop (u : unop) (v : valu) : option valu :=
  match u, v with
  | Not, Val_Bool b => Some (Val_Bool (negb b))
  | Not, _ => None
  | _, _ => (* TODO: other cases *) None
  end.

Definition eval_binop (b : binop) (v1 v2 : valu) : option valu :=
  match b, v1, v2 with
  | Eq, Val_Bool b1, Val_Bool b2 => Some (Val_Bool (eqb b1 b2))
  | _, _, _ => (* TODO: other cases *) None
  end.

Definition eval_manyop (m : manyop) (vs : list valu) : option valu :=
  match m with
  | _ => (* TODO: other cases *) None
  end.

Fixpoint eval_exp (e : exp) : option valu :=
  match e with
  | Var x _ => None
  | Bits n _ => Some (Val_Bits n)
  | Bool b _ => Some (Val_Bool b)
  | Enum em _ => Some (Val_Enum em)
  | Unop uo e' _ =>
    eval_exp e' ≫= eval_unop uo
  | Binop uo e1 e2 _ =>
    v1 ← eval_exp e1; v2 ← eval_exp e2; eval_binop uo v1 v2
  | Manyop m es _ => vs ← mapM eval_exp es; eval_manyop m vs
  | Ite e1 e2 e3 _ =>
    match eval_exp e1 with
    | Some (Val_Bool true) => eval_exp e2
    | Some (Val_Bool false) => eval_exp e3
    | _ => None
    end
  end.

Inductive label : Set :=
| LReadReg (r : register_name) (al : accessor_list) (v : valu)
| LWriteReg (r : register_name) (al : accessor_list) (v : valu)
| LDone (next : trc)
.

Inductive trace_step : trc → option label → trc → Prop :=
| DeclareConstS x v ty ann es:
    trace_step (Smt (DeclareConst x ty) ann :: es) None (subst_event x v <$> es)
| DefineConstS x e v ann es:
    eval_exp e = Some v ->
    trace_step (Smt (DefineConst x e) ann :: es) None (subst_event x v <$> es)
| AssertS e ann es:
    eval_exp e = Some (Val_Bool true) ->
    trace_step (Smt (Assert e) ann :: es) None es
| ReadRegS r al v ann es:
    trace_step (ReadReg r al v ann :: es) (Some (LReadReg r al v)) es
| WriteRegS r al v ann es:
    trace_step (WriteReg r al v ann :: es) (Some (LWriteReg r al v)) es
| DoneES es:
    trace_step [] (Some (LDone es)) es
.

Definition addr := Z.

Definition is_local_register (r : register_name) : bool :=
(* TODO: define this as something sensible, e.g. PC + R registers *)
  true.

Record seq_state := {
  seq_trace  : trc;
  seq_regs   : gmap register_name valu;
  seq_instrs : gmap addr (list trc);
}.
Instance eta_seq_state : Settable _ := settable! Build_seq_state <seq_trace; seq_regs; seq_instrs>.

Inductive seq_step : seq_state → option label → seq_state → Prop :=
| SeqNone σ t':
    trace_step σ.(seq_trace) None t' →
    seq_step σ None (σ <| seq_trace := t'|>)
| SeqReadReg σ t' al r v:
    trace_step σ.(seq_trace) (Some (LReadReg r al v)) t' →
    (if is_local_register r then σ.(seq_regs) !! r = Some v else True) →
    seq_step σ (if is_local_register r then None else (Some (LReadReg r al v))) (σ <| seq_trace := t'|>)
| SeqWriteReg σ t' al r v regs':
    trace_step σ.(seq_trace) (Some (LWriteReg r al v)) t' →
    regs' = (if is_local_register r then <[ r := v]> σ.(seq_regs) else σ.(seq_regs)) →
    seq_step σ
             (if is_local_register r then None else (Some (LWriteReg r al v)))
             (σ <| seq_trace := t'|> <| seq_regs := regs'|>)
| SeqNextInstr σ t' es:
    trace_step σ.(seq_trace) (Some (LDone es)) t' →
    (* TODO: make sure that es is one of the traces stored at pc *)
    seq_step σ None (σ <| seq_trace := t'|>)
.
