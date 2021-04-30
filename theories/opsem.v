Require Export isla.isla_lang.
From iris.program_logic Require Export language.
Open Scope Z_scope.

Definition ite {A} (b : bool) (x y : A) : A :=
  if b then x else y.
Typeclasses Opaque ite.


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
  | Val_Struct s => Val_Struct (prod_map id (subst_valu n z) <$> s)
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

Definition eval_unop (u : unop) (v : valu) : option valu :=
  match u, v with
  | Not, Val_Bool b => Some (Val_Bool (negb b))
  | Bvnot, Val_Bits n => Some (Val_Bits (bv_not n.(bvn_val)))
  | ZeroExtend z, Val_Bits n => Some (Val_Bits (bv_zero_extend z n.(bvn_val)))
  | SignExtend z, Val_Bits n => Some (Val_Bits (bv_sign_extend z n.(bvn_val)))
  | Extract u l, Val_Bits n => Some (Val_Bits (bv_extract l (u + 1 - l) n.(bvn_val)))
  | _, _ => (* TODO: other cases *) None
  end.

Definition eval_binop (b : binop) (v1 v2 : valu) : option valu :=
  match b, v1, v2 with
  | Eq, Val_Bool b1, Val_Bool b2 => Some (Val_Bool (eqb b1 b2))
  | Eq, Val_Bits n1, Val_Bits n2 => mguard (n1.(bvn_n) = n2.(bvn_n)) (λ _, Some (Val_Bool (bool_decide (n1 = n2))))
  | Bvarith Bvlshr, Val_Bits n1, Val_Bits n2 => n2' ← bvn_to_bv n1.(bvn_n) n2; Some (Val_Bits (bv_shiftr n1.(bvn_val) n2'))
  | _, _, _ => (* TODO: other cases *) None
  end.


Definition eval_manyop (m : manyop) (vs : list valu) : option valu :=
  match m, vs with
  | Bvmanyarith Bvadd, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_add n0.(bvn_val) ns)) <$>
     (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvor, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_or n0.(bvn_val) ns)) <$>
    (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvand, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_and n0.(bvn_val) ns)) <$> (
      mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Concat, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl (λ b1 b2, bv_to_bvn (bv_concat b1.(bvn_val) b2.(bvn_val))) n0 ns)) <$>
    (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
  | _, _ => (* TODO: other cases *) None
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
| LReadMem (data : valu) (kind : valu) (addr : valu) (len : N) (tag : valu_option)
| LWriteMem (res : valu) (kind : valu) (addr : valu) (data : valu) (len : N) (tag : valu_option)
| LBranchAddress (v : valu)
| LDone (next : trc)
| LAssert (b : bool)
.

Inductive trace_step : trc → option trace_label → trc → Prop :=
| DeclareConstBitVecS x n ann es b Heq:
    trace_step (Smt (DeclareConst x (Ty_BitVec b)) ann :: es) None (subst_event x (Val_Bits (BV b n Heq)) <$> es)
| DeclareConstBoolS x ann es b:
    trace_step (Smt (DeclareConst x Ty_Bool) ann :: es) None (subst_event x (Val_Bool b) <$> es)
| DefineConstS x e v ann es:
    eval_exp e = Some v ->
    trace_step (Smt (DefineConst x e) ann :: es) None (subst_event x v <$> es)
| AssertS e b ann es:
    eval_exp e = Some (Val_Bool b) ->
    trace_step (Smt (Assert e) ann :: es) (Some (LAssert b)) es
| ReadRegS r al v ann es:
    trace_step (ReadReg r al v ann :: es) (Some (LReadReg r al v)) es
| WriteRegS r al v ann es:
    trace_step (WriteReg r al v ann :: es) (Some (LWriteReg r al v)) es
| ReadMemS data kind addr len tag ann es:
    trace_step (ReadMem data kind addr len tag ann :: es) (Some (LReadMem data kind addr len tag)) es
| WriteMemS res kind addr data len tag ann es:
    trace_step (WriteMem res kind addr data len tag ann :: es) (Some (LWriteMem res kind addr data len tag)) es
| BranchAddressS v ann es:
    trace_step (BranchAddress v ann :: es) (Some (LBranchAddress v)) es
| DoneES es:
    trace_step [] (Some (LDone es)) es
.

Definition trace_module : module trace_label := {|
  m_state := trc;
  m_step := trace_step;
  m_is_ub _ := False;
|}.


Definition addr := bv 64.
Definition byte := bv 8.
(* TODO: this should probably be a simpler type than valu:
- take out poison and symbolic
- take out list and (maybe) arbitrary integer and (maybe) enum
- add unknown
 *)

Definition reg_map := gmap string valu.
Definition mem_map := gmap addr byte.

Definition instruction_size : Z := 0x4.

Definition next_pc (regs : reg_map) : option (addr * reg_map) :=
  a ← regs !! "_PC";
  an ← if a is Val_Bits n then bvn_to_bv 64 n else None;
  c ← regs !! "__PC_changed";
  cb ← if c is Val_Bool b then Some b else None;
  let new_pc := if cb : bool then bv_unsigned an else bv_unsigned an + instruction_size in
  n ← bv_of_Z_checked 64 new_pc;
  Some (n, <["_PC" := Val_Bits (BVN _ n)]> $ <["__PC_changed" := Val_Bool false]> regs).

Fixpoint read_accessor (al : accessor_list) (v : valu) : option valu :=
  match al with
  | [] => Some v
  | Field a :: al' =>
    s ← (if v is Val_Struct s then Some s else None);
    i ← (list_find_idx (λ x, x.1 = a) s);
    v' ← s !! i;
    read_accessor al' v'.2
  end.

Fixpoint write_accessor (al : accessor_list) (v : valu) (vnew : valu) : option valu :=
  match al with
  | [] => Some vnew
  | Field a :: al' =>
    s ← (if v is Val_Struct s then Some s else None);
    i ← (list_find_idx (λ x, x.1 = a) s);
    v' ← s !! i;
    (λ vnew', Val_Struct (<[i := (a, vnew')]> s))
      <$> write_accessor al' v'.2 vnew
  end.

Arguments write_accessor : simpl never.
Arguments read_accessor : simpl never.
Typeclasses Opaque write_accessor.
Typeclasses Opaque read_accessor.

Record seq_global_state := {
  seq_instrs : gmap addr (list trc);
  seq_mem    : mem_map;
}.
Instance eta_seq_global_state : Settable _ := settable! Build_seq_global_state <seq_instrs; seq_mem>.
Record seq_local_state := {
  seq_trace  : trc;
  seq_regs   : reg_map;
  seq_nb_state : bool;
}.
Instance eta_seq_local_state : Settable _ := settable! Build_seq_local_state <seq_trace; seq_regs; seq_nb_state>.

Inductive seq_label : Set :=
| SInstrTrap (pc : addr)
.

Definition read_mem_list (mem : mem_map) (a : addr) (len : N) : option (list byte) :=
  mapM (M := option) (mem !!.) (bv_seq a (Z.of_N len)).

Definition read_mem (mem : mem_map) (a : addr) (len : N) : option bvn :=
  (λ bs, BVN _ (bv_of_Z (8 * len) (bv_of_little 8 bs))) <$> read_mem_list mem a len.

Fixpoint write_mem_list (mem : mem_map) (a : addr) (v : list byte) : mem_map :=
  match v with
  | [] => mem
  | b :: bs => write_mem_list (<[a:=b]> mem) (bv_add_Z a 1) bs
  end.

Definition write_mem (len : N) (mem : mem_map) (a : addr) (v : Z) : mem_map :=
  write_mem_list mem a (bv_to_little (N.to_nat len) 8 v).

(* TODO: Maybe refactor this into several constructors rather than a match *)
Inductive seq_step : seq_local_state → seq_global_state → list seq_label → seq_local_state → seq_global_state → list seq_local_state → Prop :=
| SeqStep σ θ κ t' κ' θ' σ':
    θ.(seq_nb_state) = false →
    trace_step θ.(seq_trace) κ t' →
    match κ with
    | None => κ' = None ∧ θ' = θ <| seq_trace := t'|> ∧ σ' = σ
    | Some (LReadReg r al v) =>
      ∃ v' v'' vread,
        θ.(seq_regs) !! r = Some v' ∧
        κ' = None ∧
        read_accessor al v' = Some v'' ∧
        read_accessor al v = Some vread ∧
        σ' = σ ∧
        ((θ' = θ <| seq_trace := t'|> ∧ vread = v'') ∨ (θ' = θ <| seq_nb_state := true|>))
    | Some (LWriteReg r al v) =>
      ∃ v' v'' vnew, θ.(seq_regs) !! r = Some v' ∧
      read_accessor al v = Some vnew ∧
      write_accessor al v' vnew = Some v'' ∧
      σ' = σ ∧
      θ' = θ <| seq_trace := t'|> <| seq_regs := <[r := v'']> θ.(seq_regs)|> ∧
      κ' = None
    | Some (LReadMem data kind addr len tag) =>
      (* Ignoring tags and kinds for the time being *)
      ∃ addr' data' data'',
      addr = Val_Bits (BVN 64 addr') ∧
      data = Val_Bits (BVN (8 * len) data') ∧
      read_mem σ.(seq_mem) addr' len = Some (BVN (8 * len) data'') ∧
      κ' = None ∧
      σ' = σ ∧
       ((θ' = θ <| seq_trace := t' |> ∧ data' = data'')
        ∨ (θ' = θ <| seq_nb_state := true|>))
    | Some (LWriteMem res kind addr data len tag) =>
      (* Ignoring tags and kinds. There are no cases were the write fails *)
      ∃ mem' addr' data',
      κ' = None ∧
      addr = Val_Bits (BVN 64 addr') ∧
      data = Val_Bits (BVN (8 * len) data') ∧
      mem' = write_mem len σ.(seq_mem) addr' (bv_unsigned data') ∧
      res = Val_Bool true ∧
      σ' = σ <| seq_mem := mem' |> ∧
      θ' = θ <| seq_trace := t' |>
    | Some (LBranchAddress _) =>
      κ' = None ∧
      θ' = θ <| seq_trace := t'|> ∧
      σ' = σ
    | Some (LDone es) =>
      σ' = σ ∧
      ∃ pc regs', next_pc θ.(seq_regs) = Some (pc, regs') ∧
      match σ.(seq_instrs) !! pc with
      | Some trcs => θ' = θ <| seq_trace := t'|> <| seq_regs := regs' |> ∧ es ∈ trcs ∧ κ' = None
      | None => κ' = Some (SInstrTrap pc) ∧ θ' = θ <| seq_nb_state := true|> <| seq_regs := regs' |>
      end
    | Some (LAssert b) =>
      σ' = σ ∧
      κ' = None ∧
      θ' = θ <| seq_trace := t' |> <| seq_nb_state := negb b|>
    end →
    seq_step θ σ (option_list κ') θ' σ' []
.

Definition seq_module_no_ub  : module seq_label := {|
  m_state := _;
  m_step '(σ, θ) κ '(σ', θ') := seq_step θ σ (option_list κ) θ' σ' [];
  m_is_ub σ := False
|}.

Definition seq_module  : module seq_label := {|
  m_state := _;
  m_step '(σ, θ) κ '(σ', θ') := seq_step θ σ (option_list κ) θ' σ' [];
  m_is_ub '(σ, θ) :=
    ∃ es t', trace_step θ.(seq_trace) (Some (LDone es)) t' ∧
     ∃ θ' pc regs', next_pc θ.(seq_regs) = Some (pc, regs') ∧
      θ' = θ <| seq_trace := t'|> <| seq_regs := regs' |> ∧
      match σ.(seq_instrs) !! pc with
      | Some trcs => ¬ ∃ es κs σ'', es ∈ trcs ∧ (σ, θ' <| seq_trace := es |>) ~{seq_module_no_ub, κs}~> σ'' ∧ σ''.2.(seq_trace) = []
      | None => False
      end
  ;
|}.

Record seq_val := {
  seq_val_trace  : trc;
  seq_val_regs   : reg_map;
}.
Definition seq_of_val (v : seq_val) : seq_local_state := {|
  seq_trace := v.(seq_val_trace);
  seq_regs := v.(seq_val_regs);
  seq_nb_state := true;
|}.
Definition seq_to_val (e : seq_local_state) : option seq_val :=
  if e.(seq_nb_state) then
    Some ({|
     seq_val_trace := e.(seq_trace);
     seq_val_regs := e.(seq_regs);
    |})
  else None.

Lemma seq_lang_mixin : LanguageMixin seq_of_val seq_to_val seq_step.
Proof.
  split => //.
  - by case.
  - move => [??[]] [??] //= [ -> ->]. done.
  - move => [???] ?????. inversion 1; simplify_eq/=. done.
Qed.
Canonical Structure isla_lang := Language seq_lang_mixin.
