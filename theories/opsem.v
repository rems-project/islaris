(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Export isla.isla_lang.
From iris.program_logic Require Export language.
Open Scope Z_scope.

(* TODO: move to a separate file? *)
(*** General facts and definitions about isla_lang. *)
Inductive isla_trace : Set :=
| tnil
| tcons (e : event) (t : isla_trace)
| tcases (ts : list isla_trace).
Notation "e :t: t" := (tcons e t) (at level 60, right associativity,
 format "'[v' e  :t: '/' t ']'" ) : stdpp_scope.
Global Instance isla_trace_inhabited : Inhabited isla_trace := populate tnil.

Fixpoint subst_trace (v : base_val) (x : var_name) (t : isla_trace) :=
  match t with
  | tnil => tnil
  | tcons e t' => tcons (subst_val_event v x e) (subst_trace v x t')
  | tcases ts => tcases (subst_trace v x <$> ts)
  end.

Fixpoint isla_trace_length (t : isla_trace) : nat :=
  match t with
  | tnil => 0
  | tcons _ t' => S (isla_trace_length t')
  | tcases ts => S (sum_list (isla_trace_length <$> ts))
  end.

Definition false_trace : isla_trace := Assume (AExp_Val (AVal_Bool false) Mk_annot) Mk_annot:t:tnil.

Definition partial_trace (v : base_val) (t : isla_trace) : isla_trace :=
  match t with
  | Smt (DeclareConst x (Ty_BitVec n)) _ :t: t' =>
      match v with
      | Val_Bits b =>
          if (b.(bvn_n) =? n)%N then subst_trace v x t' else false_trace
      | _ => false_trace
      end
  | Smt (DeclareConst x Ty_Bool) _ :t: t' =>
      if v is Val_Bool _ then subst_trace v x t' else false_trace
  | _ => false_trace
  end.
Arguments partial_trace : simpl never.

Global Instance valu_inhabited : Inhabited valu := populate (RVal_Bool true).
Global Instance enum_id_eq_decision : EqDecision enum_id.
Proof. solve_decision. Qed.
Global Instance enum_ctor_eq_decision : EqDecision enum_ctor.
Proof. solve_decision. Qed.
Global Instance enum_eq_decision : EqDecision enum.
Proof. solve_decision. Qed.


Definition ite {A} (b : bool) (x y : A) : A :=
  if b then x else y.
Typeclasses Opaque ite.

Lemma ite_bv_unsigned n b (x1 x2 : bv n) :
  bv_unsigned (ite b x1 x2) = ite b (bv_unsigned x1) (bv_unsigned x2).
Proof. by destruct b. Qed.
#[export] Hint Rewrite ite_bv_unsigned : bv_unfold.

Inductive reg_kind :=
| KindReg (r : string) | KindField (r f : string).
Global Instance reg_kind_eq_decision : EqDecision reg_kind.
Proof. solve_decision. Defined.
Global Instance reg_kind_inhabited : Inhabited (reg_kind) := populate (KindReg "").
Definition reg_kind_eqb (rk1 rk2 : reg_kind) : bool :=
  match rk1, rk2 with
  | KindReg r1, KindReg r2 => (r1 =? r2)%string
  | KindField r1 f1, KindField r2 f2 => ((r1 =? r2) && (f1 =? f2))%string
  | _, _ => false
  end.
Lemma reg_kind_eqb_eq rk1 rk2:
  reg_kind_eqb rk1 rk2 = bool_decide (rk1 = rk2).
Proof. destruct rk1, rk2 => //=; rewrite !String_eqb_eq; repeat case_bool_decide; by simplify_eq. Qed.

Inductive valu_shape :=
| ExactShape (v : valu) | StructShape (ss : list (string * valu_shape)) | BitsShape (n : N) | PropShape (P : valu → Prop) | UnknownShape.
Global Instance valu_shape_inhabited : Inhabited (valu_shape) := populate UnknownShape.
Fixpoint valu_has_shape (v : valu) (s : valu_shape) : Prop :=
  match s with
  | ExactShape v' => v = v'
  | StructShape ss =>
      if v is RegVal_Struct rs then
        length ss = length rs ∧ foldr and True
          (zip_with (λ s r, s.1 = r.1 ∧ valu_has_shape r.2 s.2) ss rs)
      else False
  | BitsShape n => if v is RVal_Bits b then b.(bvn_n) = n else False
  | PropShape P => P v
  | UnknownShape => True
  end.
Arguments valu_has_shape : simpl nomatch.

Lemma valu_has_bits_shape v n:
  valu_has_shape v (BitsShape n) → ∃ b : bv n, v = RVal_Bits b.
Proof. destruct v as [[| |[]|]| | | | | | | |] => //= <-. naive_solver. Qed.

Definition valu_shape_implies (s1 s2 : valu_shape) : Prop :=
  (* TODO: add missing cases*)
  match s1, s2 with
  | ExactShape v1, _ => valu_has_shape v1 s2
  | BitsShape n1, BitsShape n2 => n1 = n2
  | _, UnknownShape => True
  | _, _ => False
  end.
Arguments valu_shape_implies _ _ : simpl nomatch.
Lemma valu_shape_implies_sound s1 s2 v:
  valu_shape_implies s1 s2 → valu_has_shape v s1 → valu_has_shape v s2.
Proof. destruct s1, s2 => //=; naive_solver. Qed.

Definition valu_shape_implies_trivial (s1 s2 : valu_shape) : bool :=
  match s1, s2 with
  | BitsShape b1, BitsShape b2 => (b1 =? b2)%N
  | _, UnknownShape => true
  | _, _ => false
  end.
Lemma valu_shape_implies_trivial_sound s1 s2:
  valu_shape_implies_trivial s1 s2 = true →
  valu_shape_implies s1 s2.
Proof. destruct s1, s2 => //= /N.eqb_eq. done. Qed.

(*** operational sematics *)

Definition addr := bv 64.
Definition byte := bv 8.
(* TODO: this should probably be a simpler type than valu:
- take out poison and symbolic
- take out list and (maybe) arbitrary integer and (maybe) enum
- add unknown
 *)

Definition reg_map := gmap string valu.
Definition mem_map := gmap addr byte.

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
  | Eq, Val_Enum n1, Val_Enum n2 =>
    Some (Val_Bool (bool_decide (n1 = n2)))

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

Definition eval_assume_val (regs : reg_map) (v : assume_val) : option base_val :=
  match v with
  | AVal_Var r l => v' ← regs !! r;
                   v'' ← read_accessor l v';
                   if v'' is RegVal_Base b then Some b else None
  | AVal_Bool b => Some (Val_Bool b)
  | AVal_Bits b => Some (Val_Bits b)
  | AVal_Enum e => Some (Val_Enum e)
  end.

Fixpoint eval_a_exp (regs : reg_map) (e : a_exp) : option base_val :=
  match e with
  | AExp_Val x _ => eval_assume_val regs x
  | AExp_Unop uo e' _ =>
    eval_a_exp regs e' ≫= eval_unop uo
  | AExp_Binop uo e1 e2 _ =>
    v1 ← eval_a_exp regs e1; v2 ← eval_a_exp regs e2; eval_binop uo v1 v2
  | AExp_Manyop m es _ => vs ← mapM (eval_a_exp regs) es; eval_manyop m vs
  | AExp_Ite e1 e2 e3 _ =>
    match eval_a_exp regs e1 with
    | Some (Val_Bool true) => eval_a_exp regs e2
    | Some (Val_Bool false) => eval_a_exp regs e3
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
| LDone (next : isla_trace)
| LAssert (b : bool)
| LAssume (b : bool)
| LAssumeReg (r : register_name) (al : accessor_list) (v : valu)
.

Inductive trace_step : isla_trace → reg_map → option trace_label → isla_trace → Prop :=
| DeclareConstBitVecS x n ann es b Heq regs:
    trace_step (Smt (DeclareConst x (Ty_BitVec b)) ann :t: es) regs None (subst_trace (Val_Bits (BV b n Heq)) x es)
| DeclareConstBoolS x ann es b regs:
    trace_step (Smt (DeclareConst x Ty_Bool) ann :t: es) regs None (subst_trace (Val_Bool b) x es)
| DeclareConstEnumS x ann es regs i c:
    trace_step (Smt (DeclareConst x (Ty_Enum i)) ann :t: es) regs None (subst_trace (Val_Enum (i, c)) x es)
| DefineConstS x e v ann es regs:
    eval_exp e = Some v ->
    trace_step (Smt (DefineConst x e) ann :t: es) regs None (subst_trace v x es)
| AssertS e b ann es regs:
    eval_exp e = Some (Val_Bool b) ->
    trace_step (Smt (Assert e) ann :t: es) regs (Some (LAssert b)) es
| AssumeS e b ann es regs:
    eval_a_exp regs e = Some (Val_Bool b) ->
    trace_step (Assume e ann :t: es) regs (Some (LAssume b)) es
| AssumeRegS r al v ann es regs:
    trace_step (AssumeReg r al v ann :t: es) regs (Some (LAssumeReg r al v)) es
| ReadRegS r al v ann es regs:
    trace_step (ReadReg r al v ann :t: es) regs (Some (LReadReg r al v)) es
| WriteRegS r al v ann es regs:
    trace_step (WriteReg r al v ann :t: es) regs (Some (LWriteReg r al v)) es
| ReadMemS data kind addr len tag ann es regs:
    trace_step (ReadMem data kind addr len tag ann :t: es) regs (Some (LReadMem data kind addr len tag)) es
| WriteMemS res kind addr data len tag ann es regs:
    trace_step (WriteMem res kind addr data len tag ann :t: es) regs (Some (LWriteMem res kind addr data len tag)) es
| BranchAddressS v ann es regs:
    trace_step (BranchAddress v ann :t: es) regs (Some (LBranchAddress v)) es
| BranchS c desc ann es regs:
    trace_step (Branch c desc ann :t: es) regs (Some (LBranch c desc)) es
| BarrierS v ann es regs :
    trace_step (Barrier v ann :t: es) regs None es
| CasesES es ts regs:
    es ∈ ts →
    trace_step (tcases ts) regs None es
| DoneES es regs:
    trace_step tnil regs (Some (LDone es)) es
.

Lemma DeclareConstBitVecS' {n} (b : bv n) x ann es regs:
  trace_step (Smt (DeclareConst x (Ty_BitVec n)) ann :t: es) regs None (subst_trace (Val_Bits b) x es).
Proof. destruct b. constructor. Qed.

Record seq_global_state := {
  seq_instrs : gmap addr isla_trace;
  seq_mem    : mem_map;
}.
Global Instance eta_seq_global_state : Settable _ := settable! Build_seq_global_state <seq_instrs; seq_mem>.
Record seq_local_state := {
  seq_trace    : isla_trace;
  seq_regs     : reg_map;
  seq_pc_reg   : register_name;
  seq_nb_state : bool;
}.
Global Instance eta_seq_local_state : Settable _ := settable! Build_seq_local_state <seq_trace; seq_regs; seq_pc_reg ;seq_nb_state>.

Inductive seq_label : Set :=
| SReadMem (a : addr) (v : bvn)
| SWriteMem (a : addr) (v : bvn)
| SInstrTrap (pc : addr)
.

Definition read_mem_list (mem : mem_map) (a : Z) (len : N) : option (list byte) :=
  mapM (M := option) (λ x, Z_to_bv_checked 64 x ≫= (mem !!.)) (seqZ a (Z.of_N len)).

Definition read_mem (mem : mem_map) (a : Z) (len : N) : option bvn :=
  (λ bs, bv_to_bvn (Z_to_bv (8 * len) (little_endian_to_bv 8 bs))) <$> read_mem_list mem a len.

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
    trace_step θ.(seq_trace) θ.(seq_regs) κ t' →
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
    | Some (LAssumeReg r al v) =>
      ∃ v',
        θ.(seq_regs) !! r = Some v' ∧
        κ' = None ∧
        read_accessor al v' = Some v ∧
        σ' = σ ∧
        θ' = θ <| seq_trace := t'|>
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
      addr = RVal_Bits (@bv_to_bvn 64 addr') ∧
      data = RVal_Bits (@bv_to_bvn (8 * len) data') ∧
      0 < Z.of_N len ∧
      (* If there is memory, we read from that memory. *)
      if read_mem σ.(seq_mem) (bv_unsigned addr') len is Some _ then
        read_mem σ.(seq_mem) (bv_unsigned addr') len = Some (@bv_to_bvn (8 * len) data'') ∧
        κ' = None ∧
        σ' = σ ∧
         ((θ' = θ <| seq_trace := t' |> ∧ data' = data'')
          ∨ (θ' = θ <| seq_nb_state := true|>))
      (* If there is no memory, we emit an event. *)
      else
        bv_unsigned addr' + Z.of_N len ≤ 2 ^ 64 ∧
        set_Forall (λ a, ¬ (bv_unsigned addr' ≤ bv_unsigned a < bv_unsigned addr' + Z.of_N len)) (dom (gset _) σ.(seq_mem)) ∧
        κ' = Some (SReadMem addr' data') ∧
        σ' = σ ∧
        θ' = θ <| seq_trace := t' |>
    | Some (LWriteMem res kind addr data len tag) =>
      (* Ignoring tags and kinds. *)
      (∃ mem' addr' data',
      addr = RVal_Bits (@bv_to_bvn 64 addr') ∧
      data = RVal_Bits (@bv_to_bvn (8 * len) data') ∧
      0 < Z.of_N len ∧
      (* If there is memory, we write to that memory. *)
      if read_mem σ.(seq_mem) (bv_unsigned addr') len is Some _ then
       (* TODO: say something about res, e.g. that there is NB if it is false? *)
        mem' = write_mem len σ.(seq_mem) addr' (bv_unsigned data') ∧
        κ' = None ∧
        σ' = σ <| seq_mem := mem' |> ∧
        θ' = θ <| seq_trace := t' |>
      (* If there is no memory, we emit an event. *)
      else
        bv_unsigned addr' + Z.of_N len ≤ 2 ^ 64 ∧
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
      ∃ pc : bv 64, θ.(seq_regs) !! θ.(seq_pc_reg) = Some (RVal_Bits pc) ∧
      match σ.(seq_instrs) !! pc with
      | Some es' => θ' = θ <| seq_trace := t'|> ∧ es = es' ∧ κ' = None
      | None => κ' = Some (SInstrTrap pc) ∧ θ' = θ <| seq_nb_state := true|>
      end
    | Some (LAssert b) =>
      σ' = σ ∧
      κ' = None ∧
      θ' = θ <| seq_trace := t' |> <| seq_nb_state := negb b|>
    | Some (LAssume b) =>
      σ' = σ ∧
      κ' = None ∧
      b = true ∧
      θ' = θ <| seq_trace := t' |> <| seq_nb_state := false|>
    end →
    seq_step θ σ (option_list κ') θ' σ' []
.

Record seq_val := {
  seq_val_trace  : isla_trace;
  seq_val_regs   : reg_map;
  seq_val_pc_reg : register_name;
}.
Definition seq_of_val (v : seq_val) : seq_local_state := {|
  seq_trace := v.(seq_val_trace);
  seq_regs := v.(seq_val_regs);
  seq_pc_reg := v.(seq_val_pc_reg);
  seq_nb_state := true;
|}.
Definition seq_to_val (e : seq_local_state) : option seq_val :=
  if e.(seq_nb_state) then
    Some ({|
     seq_val_trace := e.(seq_trace);
     seq_val_regs := e.(seq_regs);
     seq_val_pc_reg := e.(seq_pc_reg);
    |})
  else None.

Lemma seq_lang_mixin : LanguageMixin seq_of_val seq_to_val seq_step.
Proof.
  split => //.
  - by case.
  - move => [???[]] [???] //= [ -> -> ->]. done.
  - move => [????] ?????. inversion 1; simplify_eq/=. done.
Qed.
Canonical Structure isla_lang := Language seq_lang_mixin.
