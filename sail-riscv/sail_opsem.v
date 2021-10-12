Require Export isla.sail_riscv.base.
Require Export isla.sail_riscv.RV64.
Require Export isla.opsem.
Require Import isla.adequacy.
Require Import isla.riscv64.arch.

(*** Relating values *)
Definition bv_to_mword {n1 n2} (b : bv n1) `{H:ArithFact (n2 >=? 0)} : mword n2 :=
  word_to_mword (Word.NToWord _ (Z.to_N $ bv_unsigned b)).
Definition mword_to_bv {n1 n2} (b : mword n1) : bv n2 :=
  default (bv_0 _) (Z_to_bv_checked _ (Z.of_N $ Word.wordToN (get_word b))).

Lemma mword_to_bv_unsigned {n1 n2} (b : mword n1):
  n1 = Z.of_N n2 →
  bv_unsigned (mword_to_bv (n2:=n2) b) = Z.of_N (Word.wordToN (get_word b)).
Proof.
  move => Heq. rewrite /mword_to_bv/Z_to_bv_checked. case_option_guard as Hn => //=.
  contradict Hn. apply/bv_wf_in_range. unfold bv_modulus.
  have := Word.wordToN_bound (get_word b). rewrite -Npow2_pow Z_nat_N {3}Heq N2Z.id.
  rewrite -(N2Z.inj_pow 2). lia.
Qed.

Lemma mword_to_bv_add_vec {n1 : Z} {n2 : N} (b1 b2 : mword n1) :
  n1 = Z.of_N n2 →
  mword_to_bv (n2:=n2) (add_vec b1 b2) = bv_add (mword_to_bv b1) (mword_to_bv b2).
Proof.
  move => Hn. apply bv_eq.
  rewrite bv_add_unsigned !mword_to_bv_unsigned // get_word_word_binop.
  rewrite /Word.wplus /Word.wordBin Word.wordToN_NToWord_eqn.
  rewrite /bv_wrap/bv_modulus -(N2Z.inj_pow 2) -Npow2_pow Z_nat_N.
  rewrite N2Z.inj_mod. 2: { by apply: N.pow_nonzero. }
  rewrite N2Z.inj_add. f_equal. by rewrite Hn N2Z.id.
Qed.
Arguments add_vec : simpl never.


Definition register_value_to_valu (v : register_value) : valu :=
  match v with
  | Regval_bitvector_64_dec m => RVal_Bits (mword_to_bv (n2:=64) m)
  | _ => RegVal_Poison
  end.

(*** operational semantics for [monad] *)
Inductive encoded_instruction :=
| Uncompressed (i : bv 32) | Compressed (i : bv 16).

Record sail_state := SAIL {
  sail_monad : M ();
  sail_regs : regstate;
  sail_mem : mem_map;
  sail_instrs : gmap addr encoded_instruction;
  sail_stopped : bool;
}.

Definition step_cpu (i : encoded_instruction) : M () :=
  (match i with
   | Uncompressed ie => riscv.decode (bv_to_mword ie)
   | Compressed ie => riscv.decodeCompressed (bv_to_mword ie)
   end) >>=
   λ dec, execute dec >>=
   λ R, if R is RETIRE_SUCCESS then Done tt else Fail "execution failed!".


Inductive sail_step : sail_state → option seq_label → sail_state → Prop :=
| SailDone rs h i ins :
  ins !! mword_to_bv (PC rs) = Some i →
  sail_step (SAIL (Done tt) rs h ins false) None (SAIL (step_cpu i) rs h ins false)
| SailStop rs h ins :
  ins !! mword_to_bv (PC rs) = None →
  sail_step (SAIL (Done tt) rs h ins false) (Some (SInstrTrap (mword_to_bv (PC rs)))) (SAIL (Done tt) rs h ins true)
| SailChoose rs h ins e s b:
  sail_step (SAIL (Choose s e) rs h ins false) None (SAIL (e b) rs h ins false)
| SailReadReg rs h ins e r v:
  get_regval r rs = Some v →
  sail_step (SAIL (Read_reg r e) rs h ins false) None (SAIL (e v) rs h ins false)
| SailWriteReg rs rs' h ins e r v:
  set_regval r v rs = Some rs' →
  sail_step (SAIL (Write_reg r v e) rs h ins false) None (SAIL e rs' h ins false)
.

Definition sail_module := {|
  m_step := sail_step;
  m_non_ub_state σ := σ.(sail_stopped) ∨ ∃ κ σ', sail_step σ κ σ';
|}.

(*** [mctx]: Evaluation contexts for [monad] *)
Inductive mctx : Type → Type → Type :=
| NilMCtx : mctx () exception
| BindMCtx {A1 A2 E} (f : A1 → monad register_value A2 E) (K : mctx A2 E) : mctx A1 E
| TryMCtx {A E1 E2} (f : E1 → monad register_value A E2) (K : mctx A E2) : mctx A E1.

Fixpoint mctx_interp {A E} (K : mctx A E) : monad register_value A E → M () :=
  match K in (mctx A' E') return (monad register_value A' E' → M _) with
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
Definition isla_regs_wf (regs : regstate) (isla_regs : reg_map) : Prop :=
  ∀ r vi vs, isla_regs !! r = Some vi → get_regval r regs = Some vs → vi = (register_value_to_valu vs).

Record sim_state := SIM {
  sim_regs : regstate;
}.
Add Printing Constructor sim_state.
Instance eta_sim_state : Settable _ := settable! SIM <sim_regs>.

Definition sim {A E} (Σ : sim_state) (e1 : monad register_value A E) (K : mctx A E) (e2 : trc) : Prop :=
  ∀ n isla_regs mem sail_instrs isla_instrs,
  isla_regs_wf Σ.(sim_regs) isla_regs →
  (∀ sail_regs' isla_regs' mem',
      isla_regs_wf sail_regs' isla_regs' →
      dom (gset _) isla_regs' = dom _ isla_regs →
      raw_sim sail_module (iris_module isla_lang) n
          (SAIL (Done tt) sail_regs' mem' sail_instrs false)
          ({| seq_trace := []; seq_regs := isla_regs'; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem' |})) →
  raw_sim sail_module (iris_module isla_lang) n
          (SAIL (mctx_interp K e1) Σ.(sim_regs) mem sail_instrs false)
          ({| seq_trace := e2; seq_regs := isla_regs; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem |}).

Definition sim_instr (si : encoded_instruction) (ii : list trc) :=
  ∀ regs, ∃ i, i ∈ ii ∧ sim (SIM regs) (step_cpu si) NilMCtx i.

Lemma sim_implies_refines sail_instrs isla_instrs sail_regs isla_regs mem :
  dom (gset _) isla_instrs = dom (gset _) sail_instrs →
  isla_regs_wf sail_regs isla_regs →
  (∀ a si ii, sail_instrs !! a = Some si → isla_instrs !! a = Some ii → sim_instr si ii) →
  refines sail_module (SAIL (Done tt) sail_regs mem sail_instrs false)
          (iris_module isla_lang) (initial_local_state isla_regs, {| seq_instrs := isla_instrs; seq_mem := mem |}).
Proof.
  move => Hdom Hregs Hsim. apply: raw_sim_implies_refines => n.
  elim/lt_wf_ind: n sail_regs isla_regs mem Hregs.
  move => n IH sail_regs isla_regs mem Hregs.
  apply: raw_sim_safe_here => /= Hsafe.
  have {Hsafe} ? : isla_regs !! "PC" = Some (RVal_Bits (mword_to_bv (n2:=64) (PC sail_regs))). {
    destruct (isla_regs !! "PC") eqn: HPC.
    - have ->:= Hregs "PC" _ _ ltac:(done) ltac:(done). done.
    - move: Hsafe => [[]|]// [?[?[?[? Hsafe]]]]. inv_seq_step.
      revert select (∃ x, _) => -[?[??]]; unfold register_name in *; simplify_eq.
  }
  destruct (sail_instrs !! mword_to_bv (PC sail_regs)) as [si|] eqn: Hsi.
  - move: (Hsi) => /(elem_of_dom_2 _ _ _). rewrite -Hdom. move => /elem_of_dom[ii Hii]. clear Hdom.
    have [i[Hi {}Hsim]]:= Hsim _ _ _ ltac:(done) ltac:(done) sail_regs.
    apply: raw_sim_step_i. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
    apply: raw_sim_step_s. {
      econstructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: Hsim; [done|].
    move => sail_regs' isla_regs' mem' Hwf' ?.
    apply IH; [lia|done].
  - move: (Hsi) => /(not_elem_of_dom). rewrite -Hdom. move => /not_elem_of_dom Hii. clear Hdom.
    constructor => Hsafe. split. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. eexists _. split. {
      apply: (steps_l _ _ _ _ (Some _)); [| by apply: steps_refl].
      constructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: raw_sim_step_i. { by left. }
    move => ???? Hstep. inversion Hstep.
    Unshelve. exact: inhabitant.
Qed.

(*** Lemmas about [sim] *)
Lemma sim_done Σ:
  sim Σ (Done tt) NilMCtx [].
Proof. move => ?????? Hdone. by apply: Hdone. Qed.

Lemma sim_mctx_impl A1 A2 E1 E2 Σ e11 e12 K1 K2 e2:
  sim (A:=A1) (E:=E1) Σ e11 K1 e2 →
  mctx_interp K1 e11 = mctx_interp K2 e12 →
  sim (A:=A2) (E:=E2) Σ e12 K2 e2.
Proof. rewrite /sim => ? <-. done. Qed.

Lemma sim_bind A1 A2 E Σ e1 f K e2:
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2 →
  sim (A:=A2) (E:=E) Σ (e1 >>= f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.
Lemma sim_try_catch A E1 E2 Σ e1 f K e2:
  sim (A:=A) (E:=E2) Σ e1 (TryMCtx f K) e2 →
  sim (A:=A) (E:=E1) Σ (try_catch e1 f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind A1 A2 E Σ K e1 f e2:
  sim (A:=A2) Σ (e1 >>= f) K e2 →
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_catch A E1 E2 Σ K e1 f e2:
  sim (A:=A) (E:=E2) Σ (try_catch e1 f) K e2 →
  sim (A:=A) (E:=E1) Σ e1 (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind_Done A1 A2 E Σ K v f e2:
  sim (A:=A2) Σ (f v) K e2 →
  sim (A:=A1) (E:=E) Σ (Done v) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_Done A E1 E2 Σ K v f e2:
  sim (A:=A) (E:=E2) Σ (Done v) K e2 →
  sim (A:=A) (E:=E1) Σ (Done v) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_Choose {A E} Σ s e1 e2 K:
  (∀ b, sim Σ (e1 b) K e2) →
  sim (A:=A) (E:=E) Σ (Choose s e1) K e2.
Proof.
  move => Hsim ???????/=. rewrite mctx_interp_Choose.
  apply: raw_sim_step_i. { right. eexists _, _. unshelve constructor. by apply: true. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_Read_reg_l {A E} Σ r e1 e2 v K:
  get_regval r Σ.(sim_regs) = Some v →
  sim Σ (e1 v) K e2 →
  sim (A:=A) (E:=E) Σ (Read_reg r e1) K e2.
Proof.
  move => ? Hsim ???????. rewrite mctx_interp_Read_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_read_reg_l A E Σ (r : register_ref regstate register_value A) K e2:
  (v' ← get_regval (name r) Σ.(sim_regs); of_regval r v') = Some (read_from r Σ.(sim_regs)) →
  sim Σ (Done (read_from r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K e2.
Proof.
  move => /bind_Some[rv [? Hof]] Hsim.
  apply: sim_Read_reg_l; [done|] => ??. rewrite Hof.
  by apply: Hsim.
Qed.

Lemma sim_read_reg A E Σ K e2 ann r v v':
  get_regval (name r) Σ.(sim_regs) = Some v' →
  of_regval r v' = Some (read_from r Σ.(sim_regs)) →
  v = register_value_to_valu v' →
  sim (A:=A) (E:=E) Σ (Done (read_from r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K (ReadReg (name r) [] v ann :: e2).
Proof.
  move => Hget Hof -> Hsim. apply: sim_read_reg_l; [ by simplify_option_eq|].
  move => ? isla_regs ??? Hwf?.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (name r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor => //=. 1: by econstructor.
    simpl. have ?:= Hwf (name r) _ _ ltac:(done) ltac:(done). simplify_eq.
    eexists _, _, _. split_and! => //. by left. }
  by apply: Hsim.
Qed.

Lemma sim_write_reg {A E} Σ (r : register_ref _ _ A) e2 v K v' ann:
  set_regval (name r) (regval_of r v) Σ.(sim_regs) = Some (write_to r v Σ.(sim_regs)) →
  v' = register_value_to_valu (regval_of r v) →
  sim (Σ <|sim_regs := write_to r v Σ.(sim_regs)|>) (Done tt) K e2 →
  sim (E:=E) Σ (write_reg r v) K (WriteReg (name r) [] v' ann :: e2).
Proof.
  destruct Σ => /=.
  move => Hset -> Hsim ? isla_regs ? ?? Hwf Hdone. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (name r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor; [done| by econstructor|] => /=.
    eexists _, _, _. done.
  }
  apply: raw_sim_weaken; [apply Hsim => /=| ].
  - move => r' vi' vs'. destruct (decide (r' = name r)); simplify_eq.
    + rewrite lookup_insert. move: Hset => /get_set_regval. naive_solver.
    + rewrite lookup_insert_ne //. erewrite get_set_regval_ne; [|done..]. by apply: Hwf.
  - move => ???? Hdom. apply: Hdone; [done|]. by rewrite Hdom dom_insert_lookup_L.
  - lia.
Qed.

Lemma sim_assert_exp' E Σ b K e2 s:
  b = true →
  (∀ H, sim Σ (Done H) K e2) →
  sim (E:=E) Σ (assert_exp' b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp'. destruct b => //. Qed.

Lemma sim_assert_exp E Σ b K e2 s:
  b = true →
  sim Σ (Done tt) K e2 →
  sim (E:=E) Σ (assert_exp b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp. destruct b => //. Qed.

Lemma sim_DeclareConstBitVec A E Σ K e1 e2 ann x b (v : bv b):
  sim (A:=A) (E:=E) Σ e1 K (subst_val_event (Val_Bits v) x <$> e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x (Ty_BitVec b)) ann :: e2).
Proof.
  move => Hsim ???????. destruct v.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor.  done. }
  by apply: Hsim.
Qed.

Lemma sim_DefineConst A E Σ K e1 e2 ann x v e:
  eval_exp e = Some v →
  sim (A:=A) (E:=E) Σ e1 K (subst_val_event v x <$> e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DefineConst x e) ann :: e2).
Proof.
  move => ? Hsim ???????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.
