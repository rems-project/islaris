Require Export isla.isla_lang_ext.
From iris.program_logic Require Export language.
Open Scope Z_scope.

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

Definition eval_unop (u : unop) (v : valu) : option valu :=
  match u, v with
  | Not, Val_Bool b => Some (Val_Bool (negb b))
  | Bvnot, Val_Bits n => Some (Val_Bits (bv_not n))
  | ZeroExtend z, Val_Bits n => Some (Val_Bits (bv_zero_extend z n))
  | SignExtend z, Val_Bits n => Some (Val_Bits (bv_sign_extend z n))
  | Extract u l, Val_Bits n => Some (Val_Bits (bv_extract u l n))
  | _, _ => (* TODO: other cases *) None
  end.

Definition eval_binop (b : binop) (v1 v2 : valu) : option valu :=
  match b, v1, v2 with
  | Eq, Val_Bool b1, Val_Bool b2 => Some (Val_Bool (eqb b1 b2))
  | Eq, Val_Bits n1, Val_Bits n2 => Some (Val_Bool (bool_decide (n1 = n2)))
  | Bvarith Bvlshr, Val_Bits n1, Val_Bits n2 => Some (Val_Bits (bv_shr n1 n2))
  | _, _, _ => (* TODO: other cases *) None
  end.


Definition eval_manyop (m : manyop) (vs : list valu) : option valu :=
  match m, vs with
  | Bvmanyarith Bvadd, (Val_Bits n0 :: vs') => (λ ns, Val_Bits (foldl bv_add n0 ns)) <$> (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
  | Bvmanyarith Bvor, (Val_Bits n0 :: vs') => (λ ns, Val_Bits (foldl bv_or n0 ns)) <$> (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
  | Bvmanyarith Bvand, (Val_Bits n0 :: vs') => (λ ns, Val_Bits (foldl bv_and n0 ns)) <$> (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
  | Concat, (Val_Bits n0 :: vs') => (λ ns, Val_Bits (foldl bv_concat n0 ns)) <$> (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
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
| LBranchAddress (v : valu)
| LDone (next : trc)
.

Inductive trace_step : trc → option trace_label → trc → Prop :=
| DeclareConstBitVecS x n ann es b:
    trace_step (Smt (DeclareConst x (Ty_BitVec b)) ann :: es) None (subst_event x (Val_Bits [BV{b} n]) <$> es)
| DeclareConstBoolS x ann es b:
    trace_step (Smt (DeclareConst x Ty_Bool) ann :: es) None (subst_event x (Val_Bool b) <$> es)
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


Definition addr := Z.
Record reg_map := {
  _PC : valu;
  __PC_changed : valu;
  R0 : valu;
  R1 : valu;
  R30 : valu;
}.
Instance reg_map_empty : Empty reg_map := {|
  _PC := Val_Poison;
  __PC_changed := Val_Poison;
  R0 := Val_Poison;
  R1 := Val_Poison;
  R30 := Val_Poison;
|}.
Instance eta_regmap : Settable _ := settable! Build_reg_map <_PC; __PC_changed; R0; R1; R30>.
Definition register_name_to_accessor (n : register_name) : option ((reg_map → valu) * (valu → reg_map → reg_map)) :=
  if bool_decide (n = "_PC") then Some (_PC, λ v, set _PC (λ _, v)) else
  if bool_decide (n = "__PC_changed") then Some (__PC_changed, λ v, set __PC_changed (λ _, v)) else
  if bool_decide (n = "R0") then Some (R0, λ v, set R0 (λ _, v)) else
  if bool_decide (n = "R1") then Some (R1, λ v, set R1 (λ _, v)) else
  if bool_decide (n = "R30") then Some (R30, λ v, set R30 (λ _, v)) else
  None.
Arguments register_name_to_accessor : simpl nomatch.
Instance lookup_regmap : Lookup register_name valu reg_map :=
  λ k m,
  match register_name_to_accessor k with
  | Some (r,_) => Some (r m)
  | None => None
  end.
Instance insert_regmap : Insert register_name valu reg_map :=
  λ k a m,
  match register_name_to_accessor k with
  | Some (_, w) => w a m
  | None => m
  end.
Arguments insert_regmap _ _ !_ /.
Definition reg_map_to_gmap (regs : reg_map) : gmap string valu :=
  list_to_map ((λ n, (n, default Val_Poison (regs !! n))) <$> ["_PC"; "__PC_changed"; "R0"; "R1"; "R30"]).

Lemma reg_map_to_gmap_lookup r regs:
  reg_map_to_gmap regs !! r = regs !! r.
Proof.
  rewrite {2}/lookup/lookup_regmap/=/register_name_to_accessor.
  repeat (case_bool_decide; subst; [ done|]).
  by rewrite ?lookup_insert_ne.
Qed.

Lemma reg_map_to_gmap_insert r regs v vold:
  regs !! r = Some vold →
  <[r := v]> (reg_map_to_gmap regs) = reg_map_to_gmap (<[r := v]> regs).
Proof.
  move => Hold.
  rewrite {2}/insert/insert_regmap/=/register_name_to_accessor.
  destruct regs.
  repeat (case_bool_decide; subst; [
    repeat (rewrite (insert_commute _ _ _ v) /=; [|done]); rewrite insert_insert /=; done
    |]).
  exfalso. move: Hold.
  rewrite -reg_map_to_gmap_lookup ?lookup_insert_ne //.
Qed.

Definition is_local_register (r : register_name) : bool :=
  match register_name_to_accessor r with
  | Some _ => true
  | None => false
  end.

Lemma reg_map_lookup_is_local (regs : reg_map) r v:
  regs !! r = Some v → is_local_register r.
Proof. rewrite /lookup/lookup_regmap /is_local_register. by case_match. Qed.


Definition instruction_size : bv := [BV{64} 0x4].

Definition next_pc (nPC : bv) (changed : bool) : option (addr * valu * valu) :=
  let new_pc := (if changed then nPC else bv_add nPC instruction_size) in
  Some (new_pc.(bv_val), Val_Bits new_pc, Val_Bool false).

Definition next_pc_regs (regs : reg_map) : option (addr * reg_map) :=
  a ← regs !! "_PC";
  an ← if a is Val_Bits n then Some n else None;
  c ← regs !! "__PC_changed";
  cb ← if c is Val_Bool b then Some b else None;
  n ← next_pc an cb;
  Some (n.1.1, <["_PC" := n.1.2]> $ <["__PC_changed" := n.2]> regs).

Record seq_global_state := {
  seq_instrs : gmap addr (list trc);
}.
Record seq_local_state := {
  seq_trace  : trc;
  seq_regs   : reg_map;
  seq_nb_state : bool;
}.
Instance eta_seq_local_state : Settable _ := settable! Build_seq_local_state <seq_trace; seq_regs; seq_nb_state>.

Inductive seq_label : Set :=
| SReadReg (r : register_name) (al : accessor_list) (v : valu)
| SWriteReg (r : register_name) (al : accessor_list) (v : valu)
| SInstrTrap (pc : addr) (regs : reg_map)
.

Inductive seq_step : seq_local_state → seq_global_state → list seq_label → seq_local_state → seq_global_state → list seq_local_state → Prop :=
| SeqStep σ θ κ t' κ' θ':
    θ.(seq_nb_state) = false →
    trace_step θ.(seq_trace) κ t' →
    match κ with
    | None => κ' = None ∧ θ' = θ <| seq_trace := t'|>
    | Some (LReadReg r al v) =>
      if is_local_register r then
        (θ' = θ <| seq_trace := t'|> ∧
        θ.(seq_regs) !! r = Some v ∧
        κ' = None)
        ∨
        (θ' = θ <| seq_nb_state := true|> ∧ κ' = None)
      else
        θ' = θ <| seq_trace := t'|> ∧
        κ' = Some (SReadReg r al v)
    | Some (LWriteReg r al v) =>
      if is_local_register r then
        θ' = θ <| seq_trace := t'|> <| seq_regs := <[r := v]> θ.(seq_regs)|> ∧
        κ' = None
      else
        θ' = θ <| seq_trace := t'|> ∧
        κ' = Some (SWriteReg r al v)
    | Some (LBranchAddress _) => κ' = None ∧ θ' = θ <| seq_trace := t'|>
    | Some (LDone es) =>
      ∃ pc regs', next_pc_regs θ.(seq_regs) = Some (pc, regs') ∧
      θ' = θ <| seq_trace := t'|> <| seq_regs := regs' |> ∧
      match σ.(seq_instrs) !! pc with
      | Some trcs => es ∈ trcs ∧ κ' = None
      | None => κ' = Some (SInstrTrap pc regs')
      end
     end →
     seq_step θ σ (option_list κ') θ' σ []
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
     ∃ θ' pc regs', next_pc_regs θ.(seq_regs) = Some (pc, regs') ∧
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
  - move => [??[]] [??] //= [-> ->]. done.
  - move => [???] ?????. inversion 1; simplify_eq/=. done.
Qed.
Canonical Structure isla_lang := Language seq_lang_mixin.
