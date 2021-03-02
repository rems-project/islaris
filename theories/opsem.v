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

Fixpoint subst_exp (n : var_name) (v : valu) (e : exp) {struct e} : exp :=
  match e with
  | Val w a => Val (subst_valu n v w) a
  | Unop op e a => Unop op (subst_exp n v e) a
  | Binop op e1 e2 a => Binop op (subst_exp n v e1) (subst_exp n v e2) a
  | Manyop op x a => Manyop op (subst_exp n v <$> x) a
  | Ite e1 e2 e3 a => Ite (subst_exp n v e1) (subst_exp n v e2) (subst_exp n v e3) a
  end.

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
  | Branch _ _ _ | MarkReg _ _ _ | Cycle _ | Sleeping _ _ | WakeRequest _ | SleepRequest _ => e
  | Smt s ann => Smt (subst_smt n v s) ann
  | Instr i ann => Instr (subst_valu n v i) ann
  | Barrier b ann => Barrier (subst_valu n v b) ann
  | CacheOp v1 v2 ann => CacheOp (subst_valu n v v1) (subst_valu n v v2) ann
  | BranchAddress a ann => BranchAddress (subst_valu n v a) ann
  | ReadReg r al vr ann => ReadReg r al (subst_valu n v vr) ann
  | WriteReg r al vr ann => WriteReg r al (subst_valu n v vr) ann
  | ReadMem vr rkind addr len tag_value ann => ReadMem (subst_valu n v vr) (subst_valu n v rkind) (subst_valu n v addr) len (subst_valu n v <$> tag_value) ann
  | WriteMem va wkind addr data nat5 tag_value ann => WriteMem (subst_valu n v va) (subst_valu n v wkind) (subst_valu n v addr) (subst_valu n v data) nat5 (subst_valu n v <$> tag_value) ann
  end.

Definition Z_extract (i j n : Z) : Z :=
  (Z.land n (Z.ones (i + 1))) ≫ j.

Definition eval_unop (u : unop) (v : valu) : option valu :=
  match u, v with
  | Not, Val_Bool b => Some (Val_Bool (negb b))
  | ZeroExtend _, Val_Bits n => Some (Val_Bits n)
  | Extract u l, Val_Bits n => Some (Val_Bits (Z_extract u l n))
  | _, _ => (* TODO: other cases *) None
  end.

Definition eval_binop (b : binop) (v1 v2 : valu) : option valu :=
  match b, v1, v2 with
  | Eq, Val_Bool b1, Val_Bool b2 => Some (Val_Bool (eqb b1 b2))
  | _, _, _ => (* TODO: other cases *) None
  end.

Definition eval_manyop (m : manyop) (vs : list valu) : option valu :=
  match m with
  | Bvmanyarith Bvadd => (λ ns, Val_Bits (foldl Z.add 0 ns)) <$> (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs)
  | _ => (* TODO: other cases *) None
  end.

Fixpoint eval_exp (e : exp) : option valu :=
  match e with
  | Val x _ => Some x
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

Inductive trace_label : Set :=
| LReadReg (r : register_name) (al : accessor_list) (v : valu)
| LWriteReg (r : register_name) (al : accessor_list) (v : valu)
| LDone (next : trc)
.

Inductive trace_step : trc → option trace_label → trc → Prop :=
| DeclareConstS v x ty ann es:
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

Definition trace_module : module trace_label := {|
  m_state := trc;
  m_initial := [];
  m_step := trace_step;
  m_is_ub _ := False;
|}.


Definition addr := Z.

Definition is_local_register (r : register_name) : bool :=
(* TODO: define this as something sensible, e.g. PC + R registers *)
  true.

Definition next_pc (regs : gmap register_name valu) : (addr * gmap register_name valu).
Admitted.

Record seq_state := {
  seq_trace  : trc;
  seq_regs   : gmap register_name valu;
  seq_instrs : gmap addr (list trc);
}.
Instance eta_seq_state : Settable _ := settable! Build_seq_state <seq_trace; seq_regs; seq_instrs>.

Inductive seq_label : Set :=
| SReadReg (r : register_name) (al : accessor_list) (v : valu)
| SWriteReg (r : register_name) (al : accessor_list) (v : valu)
| SInstrTrap (pc : addr)
.

Inductive seq_step : seq_state → option seq_label → seq_state → Prop :=
| SeqNone σ t':
    trace_step σ.(seq_trace) None t' →
    seq_step σ None (σ <| seq_trace := t'|>)
| SeqReadReg σ t' al r v:
    trace_step σ.(seq_trace) (Some (LReadReg r al v)) t' →
    (if is_local_register r then σ.(seq_regs) !! r = Some v else True) →
    seq_step σ (if is_local_register r then None else (Some (SReadReg r al v))) (σ <| seq_trace := t'|>)
| SeqWriteReg σ t' al r v regs':
    trace_step σ.(seq_trace) (Some (LWriteReg r al v)) t' →
    regs' = (if is_local_register r then <[ r := v]> σ.(seq_regs) else σ.(seq_regs)) →
    seq_step σ
             (if is_local_register r then None else (Some (SWriteReg r al v)))
             (σ <| seq_trace := t'|> <| seq_regs := regs'|>)
| SeqNextInstr σ t' es regs' pc trcs:
    trace_step σ.(seq_trace) (Some (LDone es)) t' →
    next_pc σ.(seq_regs) = (pc, regs') →
    σ.(seq_instrs) !! pc = Some trcs →
    es ∈ trcs →
    seq_step σ None (σ <| seq_trace := t'|> <| seq_regs := regs' |>)
| SeqNextInstrTrap σ t' es regs' pc:
    trace_step σ.(seq_trace) (Some (LDone es)) t' →
    next_pc σ.(seq_regs) = (pc, regs') →
    σ.(seq_instrs) !! pc = None →
    seq_step σ (Some (SInstrTrap pc)) (σ <| seq_trace := t'|> <| seq_regs := regs' |>)
.
