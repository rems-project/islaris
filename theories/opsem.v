Require Export isla.isla_lang.
From iris.program_logic Require Export language.
Open Scope Z_scope.

Global Instance valu_inhabited : Inhabited valu := populate (RVal_Bool true).

Definition ite {A} (b : bool) (x y : A) : A :=
  if b then x else y.
Typeclasses Opaque ite.

Lemma ite_bv_unsigned n b (x1 x2 : bv n) :
  bv_unsigned (ite b x1 x2) = ite b (bv_unsigned x1) (bv_unsigned x2).
Proof. by destruct b. Qed.
Hint Rewrite ite_bv_unsigned : bv_unfold.

Inductive reg_kind :=
| KindReg (r : string) | KindField (r f : string).
Global Instance reg_kind_eq_decision : EqDecision reg_kind.
Proof. solve_decision. Defined.

Inductive valu_shape :=
| ExactShape (v : valu) | BitsShape (n : N) | UnknownShape.
Definition valu_has_shape (v : valu) (s : valu_shape) : Prop :=
  match s with
  | ExactShape v' => v = v'
  | BitsShape n => if v is RVal_Bits b then b.(bvn_n) = n else False
  | UnknownShape => True
  end.
Arguments valu_has_shape : simpl nomatch.

Lemma valu_has_bits_shape v n:
  valu_has_shape v (BitsShape n) → ∃ b : bv n, v = RVal_Bits b.
Proof. destruct v as [[| |[]|]| | | | | | | |] => //= <-. naive_solver. Qed.

Definition eval_unop (u : unop) (v : base_val) : option base_val :=
  match u, v with
  | Not, Val_Bool b => Some (Val_Bool (negb b))
  | Bvnot, Val_Bits n => Some (Val_Bits (bv_not n.(bvn_val)))
  | Bvneg, Val_Bits n => Some (Val_Bits (bv_opp n.(bvn_val)))
  | ZeroExtend z, Val_Bits n => Some (Val_Bits (bv_zero_extend (z + n.(bvn_n)) n.(bvn_val)))
  | SignExtend z, Val_Bits n => Some (Val_Bits (bv_sign_extend (z + n.(bvn_n)) n.(bvn_val)))
  | Extract u l, Val_Bits n => Some (Val_Bits (bv_extract l (u + 1 - l) n.(bvn_val)))
  | _, _ => None
  end.

Definition eval_binop (b : binop) (v1 v2 : base_val) : option base_val :=
  match b, v1, v2 with
  | Eq, Val_Bool b1, Val_Bool b2 =>
    Some (Val_Bool (eqb b1 b2))
  | Eq, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bool (bool_decide (n1.(bvn_val) = n2')))

  (* TODO: add support for Bvnand, Bvnor, Bvxnor *)

  | Bvarith Bvsub, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_sub n1.(bvn_val) n2'))
  (* TODO: what is the difference between Bvudiv and Bvudivi? *)
  | Bvarith Bvudiv, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_divu n1.(bvn_val) n2'))
  (* TODO: what is the difference between Bvsdiv and Bvsdivi? *)
  | Bvarith Bvsdiv, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_quots n1.(bvn_val) n2'))
  | Bvarith Bvurem, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_modu n1.(bvn_val) n2'))
  | Bvarith Bvsrem, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_rems n1.(bvn_val) n2'))
  | Bvarith Bvsmod, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_mods n1.(bvn_val) n2'))
  | Bvarith Bvshl, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_shiftl n1.(bvn_val) n2'))
  | Bvarith Bvlshr, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_shiftr n1.(bvn_val) n2'))
  | Bvarith Bvashr, Val_Bits n1, Val_Bits n2 =>
    n2' ← bvn_to_bv n1.(bvn_n) n2;
    Some (Val_Bits (bv_ashiftr n1.(bvn_val) n2'))

  | Bvcomp Bvult, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_unsigned n1.(bvn_val) < bv_unsigned n2.(bvn_val))))
  | Bvcomp Bvslt, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_signed n1.(bvn_val) < bv_signed n2.(bvn_val))))
  | Bvcomp Bvule, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_unsigned n1.(bvn_val) ≤ bv_unsigned n2.(bvn_val))))
  | Bvcomp Bvsle, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_signed n1.(bvn_val) ≤ bv_signed n2.(bvn_val))))
  | Bvcomp Bvuge, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_unsigned n1.(bvn_val) >= bv_unsigned n2.(bvn_val))))
  | Bvcomp Bvsge, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_signed n1.(bvn_val) >= bv_signed n2.(bvn_val))))
  | Bvcomp Bvugt, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_unsigned n1.(bvn_val) > bv_unsigned n2.(bvn_val))))
  | Bvcomp Bvsgt, Val_Bits n1, Val_Bits n2 =>
    guard (n1.(bvn_n) = n2.(bvn_n));
    Some (Val_Bool (bool_decide (bv_signed n1.(bvn_val) > bv_signed n2.(bvn_val))))
  | _, _, _ => None
  end.


Definition eval_manyop (m : manyop) (vs : list base_val) : option base_val :=
  match m, vs with
  | Bvmanyarith Bvand, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_and n0.(bvn_val) ns)) <$> (
      mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvor, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_or n0.(bvn_val) ns)) <$>
    (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvxor, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_xor n0.(bvn_val) ns)) <$>
    (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvadd, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_add n0.(bvn_val) ns)) <$>
     (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Bvmanyarith Bvmul, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl bv_mul n0.(bvn_val) ns)) <$>
     (mapM (M := option) (λ v, match v with | Val_Bits n => bvn_to_bv n0.(bvn_n) n | _ => None end ) vs')
  | Concat, (Val_Bits n0 :: vs') =>
    (λ ns, Val_Bits (foldl (λ b1 b2, bv_to_bvn (bv_concat (b1.(bvn_n) + b2.(bvn_n)) b1.(bvn_val) b2.(bvn_val))) n0 ns)) <$>
    (mapM (M := option) (λ v, match v with | Val_Bits n => Some n | _ => None end ) vs')
  | _, _ => (* TODO: And, Or *) None
  end.

Fixpoint eval_exp (e : exp) : option base_val :=
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
| LBranch (c : Z) (desc : string)
| LDone (next : trc)
| LAssert (b : bool)
.

Inductive trace_step : trc → option trace_label → trc → Prop :=
| DeclareConstBitVecS x n ann es b Heq:
    trace_step (Smt (DeclareConst x (Ty_BitVec b)) ann :: es) None (subst_val_event (Val_Bits (BV b n Heq)) x <$> es)
| DeclareConstBoolS x ann es b:
    trace_step (Smt (DeclareConst x Ty_Bool) ann :: es) None (subst_val_event (Val_Bool b) x <$> es)
| DefineConstS x e v ann es:
    eval_exp e = Some v ->
    trace_step (Smt (DefineConst x e) ann :: es) None (subst_val_event v x <$> es)
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
| BranchS c desc ann es:
    trace_step (Branch c desc ann :: es) (Some (LBranch c desc)) es
| DoneES es:
    trace_step [] (Some (LDone es)) es
.

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
  an ← if a is RVal_Bits n then bvn_to_bv 64 n else None;
  c ← regs !! "__PC_changed";
  cb ← if c is RVal_Bool b then Some b else None;
  let new_pc := if cb : bool then bv_unsigned an else bv_unsigned an + instruction_size in
  n ← Z_to_bv_checked 64 new_pc;
  Some (n, <["_PC" := RVal_Bits (BVN _ n)]> $ <["__PC_changed" := RVal_Bool false]> regs).

Fixpoint read_accessor (al : accessor_list) (v : valu) : option valu :=
  match al with
  | [] => Some v
  | Field a :: al' =>
    s ← (if v is RegVal_Struct s then Some s else None);
    i ← (list_find_idx (λ x, x.1 = a) s);
    v' ← s !! i;
    read_accessor al' v'.2
  end.

Fixpoint write_accessor (al : accessor_list) (v : valu) (vnew : valu) : option valu :=
  match al with
  | [] => Some vnew
  | Field a :: al' =>
    s ← (if v is RegVal_Struct s then Some s else None);
    i ← (list_find_idx (λ x, x.1 = a) s);
    v' ← s !! i;
    (λ vnew', RegVal_Struct (<[i := (a, vnew')]> s))
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
| SWriteMem (a : addr) (v : bvn)
| SInstrTrap (pc : addr)
.

Definition read_mem_list (mem : mem_map) (a : addr) (len : N) : option (list byte) :=
  mapM (M := option) (mem !!.) (bv_seq a (Z.of_N len)).

Definition read_mem (mem : mem_map) (a : addr) (len : N) : option bvn :=
  (λ bs, BVN _ (Z_to_bv (8 * len) (little_endian_to_bv 8 bs))) <$> read_mem_list mem a len.

Fixpoint write_mem_list (mem : mem_map) (a : addr) (v : list byte) : mem_map :=
  match v with
  | [] => mem
  | b :: bs => write_mem_list (<[a:=b]> mem) (bv_add_Z a 1) bs
  end.

Definition write_mem (len : N) (mem : mem_map) (a : addr) (v : Z) : mem_map :=
  write_mem_list mem a (bv_to_little_endian (N.to_nat len) 8 v).

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
      addr = RVal_Bits (BVN 64 addr') ∧
      data = RVal_Bits (BVN (8 * len) data') ∧
      0 < Z.of_N len ∧
      read_mem σ.(seq_mem) addr' len = Some (BVN (8 * len) data'') ∧
      κ' = None ∧
      σ' = σ ∧
       ((θ' = θ <| seq_trace := t' |> ∧ data' = data'')
        ∨ (θ' = θ <| seq_nb_state := true|>))
    | Some (LWriteMem res kind addr data len tag) =>
      (* Ignoring tags and kinds. *)
      (∃ mem' addr' data',
      addr = RVal_Bits (BVN 64 addr') ∧
      data = RVal_Bits (BVN (8 * len) data') ∧
      0 < Z.of_N len ∧
      (* If there is memory, we write to that memory. *)
      if read_mem σ.(seq_mem) addr' len is Some _ then
       (* TODO: say something about res, e.g. that there is NB if it is false? *)
        mem' = write_mem len σ.(seq_mem) addr' (bv_unsigned data') ∧
        κ' = None ∧
        σ' = σ <| seq_mem := mem' |> ∧
        θ' = θ <| seq_trace := t' |>
      (* If there is no memory, we emit an event. *)
      else
        set_Forall (λ a, ¬ (bv_unsigned addr' ≤ bv_unsigned a < bv_unsigned addr' + Z.of_N len)) (dom (gset _) σ.(seq_mem)) ∧
        κ' = Some (SWriteMem addr' data') ∧
        σ' = σ ∧
        θ' = θ <| seq_trace := t' |>
      )
    | Some (LBranchAddress _) =>
      κ' = None ∧
      θ' = θ <| seq_trace := t'|> ∧
      σ' = σ
    | Some (LBranch _ _) =>
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
