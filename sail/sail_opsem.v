Require Export Sail.Base.
Require Export Sail.Prompt_monad.
Require Export aarch64.aarch64_types.
Require Export aarch64.aarch64_extras.
Require Export aarch64.aarch64.
Require Export isla.sail.base.
Require Export isla.opsem.
Require Import isla.adequacy.

(*** Relating values *)
Definition bv_to_mword {n1 n2} (b : bv n1) `{H:ArithFact (n2 >=? 0)} : mword n2 :=
  word_to_mword (Word.ZToWord _ (bv_unsigned b)).
Definition mword_to_bv {n1 n2} (b : mword n1) : bv n2.
Admitted.
Definition valu_to_register_value (v : valu) : option register_value.
Admitted.

(*** operational semantics for [monad] *)
Record sail_state := SAIL {
  sail_monad : M unit;
  sail_regs : regstate;
  sail_mem : mem_map;
}.

Inductive sail_step : sail_state → option seq_label → sail_state → Prop :=
| SailDone rs h :
  sail_step (SAIL (Done tt) rs h) None (SAIL (Step_CPU tt) rs h)
| SailChoose rs h e s b:
  sail_step (SAIL (Choose s e) rs h) None (SAIL (e b) rs h)
| SailReadReg rs h e r v:
  get_regval r rs = Some v →
  sail_step (SAIL (Read_reg r e) rs h) None (SAIL (e v) rs h)
| SailWriteReg rs rs' h e r v:
  set_regval r v rs = Some rs' →
  sail_step (SAIL (Write_reg r v e) rs h) None (SAIL e rs' h)
.

Definition sail_module := {|
  m_step := sail_step;
  m_non_ub_state σ := ∃ κ σ', sail_step σ κ σ';
|}.

(*** [mctx]: Evaluation contexts for [monad] *)
Inductive mctx : Type → Type → Type :=
| NilMCtx : mctx unit exception
| BindMCtx {A1 A2 E} (f : A1 → monad register_value A2 E) (K : mctx A2 E) : mctx A1 E
| TryMCtx {A E1 E2} (f : E1 → monad register_value A E2) (K : mctx A E2) : mctx A E1.

Fixpoint mctx_interp {A E} (K : mctx A E) : monad register_value A E → M () :=
  match K in (mctx A' E') return (monad register_value A' E' → M ()) with
   | NilMCtx => λ e, e
   | BindMCtx f K => λ e, mctx_interp K (e >>= f)
   | TryMCtx f K => λ e, mctx_interp K (try_catch e f)
   end.

Lemma mctx_interp_Choose A E K s e1:
  @mctx_interp A E K (Choose s e1) = Choose s (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Read_reg A E K r e1:
  @mctx_interp A E K (Read_reg r e1) = Read_reg r (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_reg A E K r e1 v:
  @mctx_interp A E K (Write_reg r v e1) = Write_reg r v (mctx_interp K e1).
Proof. elim: K e1 => //=. Qed.

(*** [sim]: Simulation relation *)
Definition isla_regs_wf (regs : regstate) (mapped_regs : gset string) (isla_regs : reg_map) : Prop.
Admitted.

Definition mem_add_instrs (mem : mem_map) (instrs : gmap addr (bv 32)) : mem_map.
Admitted.

Record sim_state := SIM {
  sim_regs : regstate;
  sim_mapped_regs : gset string;
  sim_mem : mem_map;
  sim_instrs : gmap addr (bv 32 * list trc);
}.
Add Printing Constructor sim_state.
Instance eta_sim_state : Settable _ := settable! SIM <sim_regs; sim_mapped_regs; sim_mem; sim_instrs>.

Definition sim {A E} (n : nat) (Σ : sim_state) (e1 : monad register_value A E) (K : mctx A E)  (e2 : trc) : Prop :=
  ∀ isla_regs,
  isla_regs_wf Σ.(sim_regs) Σ.(sim_mapped_regs) isla_regs →
  raw_sim sail_module (iris_module isla_lang) n
          (SAIL (mctx_interp K e1) Σ.(sim_regs) (mem_add_instrs Σ.(sim_mem) (fst <$> Σ.(sim_instrs))))
          ({| seq_trace := e2; seq_regs := isla_regs; seq_nb_state := false|},
            {| seq_instrs := snd <$> Σ.(sim_instrs); seq_mem := Σ.(sim_mem) |}).

Lemma sim_implies_refines instr_opcodes isla_regs sail_regs mem instrs:
  dom (gset _) instrs = dom (gset _) instr_opcodes →
  isla_regs_wf sail_regs (dom _ isla_regs) isla_regs →
  (∀ n, sim n (SIM sail_regs (dom _ isla_regs) mem (map_zip instr_opcodes instrs) ) (Done tt) NilMCtx []) →
  refines sail_module (SAIL (Done tt) sail_regs (mem_add_instrs mem instr_opcodes))
          (iris_module isla_lang) (initial_local_state isla_regs, {| seq_instrs := instrs; seq_mem := mem |}).
Proof.
  move => Hdom ? Hsim. apply: raw_sim_implies_refines => n. move: (Hsim n).
  rewrite /sim/= fst_map_zip. 2: { intros ? ?%elem_of_dom. apply elem_of_dom. by rewrite Hdom. }
  rewrite snd_map_zip. 2: { intros ? ?%elem_of_dom. apply elem_of_dom. by rewrite -Hdom. }
  by apply.
Qed.

(*** Lemmas about [sim] *)
Lemma sim_mctx_impl A1 A2 E1 E2 n Σ e11 e12 K1 K2 e2:
  sim (A:=A1) (E:=E1) n Σ e11 K1 e2 →
  mctx_interp K1 e11 = mctx_interp K2 e12 →
  sim (A:=A2) (E:=E2) n Σ e12 K2 e2.
Proof. rewrite /sim => ? <-. done. Qed.

Lemma sim_bind A1 A2 E n Σ e1 f K e2:
  sim (A:=A1) (E:=E) n Σ e1 (BindMCtx f K) e2 →
  sim (A:=A2) (E:=E) n Σ (e1 >>= f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.
Lemma sim_try_catch A E1 E2 n Σ e1 f K e2:
  sim (A:=A) (E:=E2) n Σ e1 (TryMCtx f K) e2 →
  sim (A:=A) (E:=E1) n Σ (try_catch e1 f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind A1 A2 E n Σ K e1 f e2:
  sim (A:=A2) n Σ (e1 >>= f) K e2 →
  sim (A:=A1) (E:=E) n Σ e1 (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_catch A E1 E2 n Σ K e1 f e2:
  sim (A:=A) (E:=E2) n Σ (try_catch e1 f) K e2 →
  sim (A:=A) (E:=E1) n Σ e1 (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind_Done A1 A2 E n Σ K v f e2:
  sim (A:=A2) n Σ (f v) K e2 →
  sim (A:=A1) (E:=E) n Σ (Done v) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_Done A E1 E2 n Σ K v f e2:
  sim (A:=A) (E:=E2) n Σ (Done v) K e2 →
  sim (A:=A) (E:=E1) n Σ (Done v) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_Step_CPU n Σ e2:
  (∀ n', n = S n' → sim n' Σ (Step_CPU tt) NilMCtx e2) →
  sim n Σ (Done tt) NilMCtx e2.
Proof.
  move => Hsim ??.
  apply: raw_sim_step_i. { eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  by apply: Hsim.
Qed.

Lemma sim_Choose {A E} n Σ s e1 e2 K:
  (∀ n' b, n = S n' → sim n' Σ (e1 b) K e2) →
  sim (A:=A) (E:=E) n Σ (Choose s e1) K e2.
Proof.
  move => Hsim ??/=. rewrite mctx_interp_Choose.
  apply: raw_sim_step_i. { eexists _, _. unshelve constructor. by apply: true. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  by apply: Hsim.
Qed.

Lemma sim_Read_reg {A E} n Σ r e1 e2 v K:
  get_regval r Σ.(sim_regs) = Some v →
  (∀ n', n = S n' → sim n' Σ (e1 v) K e2) →
  sim (A:=A) (E:=E) n Σ (Read_reg r e1) K e2.
Proof.
  move => ? Hsim ??. rewrite mctx_interp_Read_reg.
  apply: raw_sim_step_i. { eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  by apply: Hsim.
Qed.

Lemma sim_read_reg A E n Σ (r : register_ref regstate register_value A) K e2:
  (v' ← get_regval (name r) Σ.(sim_regs); of_regval r v') = Some (read_from r Σ.(sim_regs)) →
  (∀ n', n = S n' → sim n' Σ (Done (read_from r Σ.(sim_regs))) K e2) →
  sim (A:=A) (E:=E) n Σ (read_reg r) K e2.
Proof.
  move => /bind_Some[rv [? Hof]] Hsim.
  apply: sim_Read_reg; [done|] => ??. rewrite Hof. by apply: Hsim.
Qed.

Lemma sim_Write_reg {A E} n Σ regs' r e1 e2 v K:
  set_regval r v Σ.(sim_regs) = Some regs' →
  (∀ n', n = S n' → sim n' (Σ <|sim_regs := regs'|>) e1 K e2) →
  sim (A:=A) (E:=E) n Σ (Write_reg r v e1) K e2.
Proof.
  move => ? Hsim ??. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: Hsim; [done|].
Admitted.

Lemma sim_write_reg A E n Σ (r : register_ref regstate _ A) K e2 v:
  set_regval (name r) (regval_of r v) Σ.(sim_regs) = Some (write_to r v Σ.(sim_regs)) →
  (∀ n', n = S n' → sim n' (Σ <|sim_regs := write_to r v Σ.(sim_regs)|>) (Done tt) K e2) →
  sim (E:=E) n Σ (write_reg r v) K e2.
Proof. move => Hset Hsim. apply: sim_Write_reg; [done|] => ??. by apply: Hsim. Qed.

Lemma sim_assert_exp' E n Σ b K e2 s:
  b = true →
  (∀ H, sim n Σ (Done H) K e2) →
  sim (E:=E) n Σ (assert_exp' b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp'. destruct b => //. Qed.

Lemma sim_assert_exp E n Σ b K e2 s:
  b = true →
  (sim n Σ (Done tt) K e2) →
  sim (E:=E) n Σ (assert_exp b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp. destruct b => //. Qed.
