From iris.proofmode Require Import coq_tactics reduction.
From refinedc.lithium Require Export lithium tactics.
From isla Require Export lifting bitvector_auto.
Set Default Proof Using "Type".

(** * Simplification and normalization hints *)
(* TODO: upstream *)
  Global Instance simpl_existT A (P : A → Type) p (x y : P p) `{!EqDecision A}:
    SimplBoth (existT p x = existT p y) (x = y).
  Proof. split; [|naive_solver]. apply Eqdep_dec.inj_pair2_eq_dec => ??. apply decide. apply _. Qed.

Create HintDb isla_coq_rewrite discriminated.
Lemma ite_bits n b (n1 n2 : bv n) :
  ite b (Val_Bits n1) (Val_Bits n2) = Val_Bits (ite b n1 n2).
Proof. by destruct b. Qed.
#[export] Hint Rewrite ite_bits : isla_coq_rewrite.
#[export] Hint Rewrite Z_to_bv_checked_bv_unsigned : isla_coq_rewrite.

#[export] Hint Rewrite bool_to_Z_Z_of_bool : isla_coq_rewrite.
#[export] Hint Rewrite @bv_extract_concat_later @bv_extract_concat_here using lia : isla_coq_rewrite.

Global Instance simpl_both_prefix_nil {A} (κs : list A):
  SimplBoth ([] `prefix_of` κs) True.
Proof. split => // ?. apply: prefix_nil. Qed.
Global Instance simpl_both_prefix_cons {A} (κ1 : A) κs1 κ2 κs2:
  SimplBoth (κ1::κs1 `prefix_of` κ2::κs2) (κ1 = κ2 ∧ κs1 `prefix_of` κs2).
Proof.
  split.
  - move => Hp. move: Hp (Hp) => /(prefix_cons_inv_1 _ _)? /(prefix_cons_inv_2 _ _)?. done.
  - move => [-> ?]. by apply: prefix_cons.
Qed.

Global Instance simpl_val_bits_bv_to_bvn n (b1 b2 : bv n) :
  SimplBoth (Val_Bits b1 = Val_Bits b2) (b1 = b2).
Proof. split; naive_solver. Qed.

Global Instance simpl_val_bool b1 b2 :
  SimplBoth (Val_Bool b1 = Val_Bool b2) (b1 = b2).
Proof. split; naive_solver. Qed.

Global Instance simple_regval_to_base_val (v1 v2 : base_val) :
  SimplBoth (RegVal_Base v1 = RegVal_Base v2) (v1 = v2).
Proof. split; naive_solver. Qed.

Global Instance simpl_bvn_eq (b1 b2 : bvn) {Heq : TCEq b2.(bvn_n) b1.(bvn_n)}:
  SimplBoth (b1 = b2) (b1.(bvn_val) = TCEq_rect _ _ (λ x, bv x) b2.(bvn_val) _ Heq).
Proof.
  split.
  - move => ?. subst. apply bv_eq. by destruct Heq => /=.
  - move => Hb. apply bvn_eq. move: Hb => /bv_eq. by destruct Heq => /= ?.
Qed.
Global Instance simpl_bvn_neq (b1 b2 : bvn) {Heq : TCEq b2.(bvn_n) b1.(bvn_n)}:
  SimplBoth (b1 ≠ b2) (b1.(bvn_val) ≠ TCEq_rect _ _ (λ x, bv x) b2.(bvn_val) _ Heq).
Proof.
  split.
  - move => Hb Hbn. apply: Hb. apply bvn_eq. move: Hbn => /bv_eq.
    by destruct Heq => /=.
  - move => Hb. contradict Hb. subst. apply bv_eq. by destruct Heq.
Qed.

Global Instance ite_1_0_eq_1_simpl b :
  SimplBoth (ite b [BV{1} 1] [BV{1} 0] = [BV{1} 1]) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_1_0_neq_1_simpl b :
  SimplBoth (ite b [BV{1} 1] [BV{1} 0] ≠ [BV{1} 1]) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_1_0_eq_0_simpl b :
  SimplBoth (ite b [BV{1} 1] [BV{1} 0] = [BV{1} 0]) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_1_0_neq_0_simpl b :
  SimplBoth (ite b [BV{1} 1] [BV{1} 0] ≠ [BV{1} 0]) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_eq_1_simpl b :
  SimplBoth (ite b [BV{1} 0] [BV{1} 1] = [BV{1} 1]) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_0_1_neq_1_simpl b :
  SimplBoth (ite b [BV{1} 0] [BV{1} 1] ≠ [BV{1} 1]) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_eq_0_simpl b :
  SimplBoth (ite b [BV{1} 0] [BV{1} 1] = [BV{1} 0]) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_neq_0_simpl b :
  SimplBoth (ite b [BV{1} 0] [BV{1} 1] ≠ [BV{1} 0]) (b = false).
Proof. by destruct b. Qed.

Global Instance simpl_bool_to_bv_1 n b1 b2 `{!TCDone (n ≠ 0%N ∧ bv_unsigned b2 = 1)}:
  SimplBothRel (=) (bool_to_bv n b1) b2 (b1 = true).
Proof.
  unfold TCDone in *. split; rewrite bv_eq; rewrite bool_to_bv_unsigned //; destruct b1 => //=; lia.
Qed.
Global Instance simpl_bool_to_bv_0 n b1 b2 `{!TCDone (n ≠ 0%N ∧ bv_unsigned b2 = 0)}:
  SimplBothRel (=) (bool_to_bv n b1) b2 (b1 = false).
Proof.
  unfold TCDone in *. split; rewrite bv_eq; rewrite bool_to_bv_unsigned //; destruct b1 => //=; lia.
Qed.
Global Instance simpl_bool_to_bv_neq_1 n b1 b2 `{!TCDone (n ≠ 0%N ∧ bv_unsigned b2 = 1)}:
  SimplBoth (bool_to_bv n b1 ≠ b2) (b1 = false).
Proof.
  unfold TCDone in *. split; rewrite bv_eq; rewrite bool_to_bv_unsigned //; destruct b1 => //=; lia.
Qed.
Global Instance simpl_bool_to_bv_neq_0  n b1 b2 `{!TCDone (n ≠ 0%N ∧ bv_unsigned b2 = 0)}:
  SimplBoth (bool_to_bv n b1 ≠ b2) (b1 = true).
Proof.
  unfold TCDone in *. split; rewrite bv_eq; rewrite bool_to_bv_unsigned //; destruct b1 => //=; lia.
Qed.

Global Instance simpl_SWriteMem a1 a2 v1 v2:
  SimplBoth (SWriteMem a1 v1 = SWriteMem a2 v2) (a1 = a2 ∧ v1 = v2).
Proof. split; naive_solver. Qed.
Global Instance simpl_SReadMem a1 a2 v1 v2:
  SimplBoth (SReadMem a1 v1 = SReadMem a2 v2) (a1 = a2 ∧ v1 = v2).
Proof. split; naive_solver. Qed.
Global Instance simpl_SInstrTrap a1 a2:
  SimplBoth (SInstrTrap a1 = SInstrTrap a2) (a1 = a2).
Proof. split; naive_solver. Qed.

Global Instance simpl_impl_valu_has_shape_bits v n:
  SimplImpl true (valu_has_shape v (BitsShape n)) (λ T, ∀ b : bv n, v = RVal_Bits b → T).
Proof. move => ?. split; [| naive_solver]. move => Hb /valu_has_bits_shape. naive_solver. Qed.
(* unsafe because proving both directions is annoying *)
Global Instance simpl_impl_valu_struct_shape v ss :
  SimplImplUnsafe true (valu_has_shape v (StructShape ss)) (λ T,
    foldr (λ s (T : _ → Prop) rs, ∀ v, valu_has_shape v s.2 → T (rs ++ [(s.1, v)])) (λ rs, v = RegVal_Struct rs → T) ss []).
Proof.
  move => T. move Hrs': {2}[] => rs'.
  destruct v as [| | | | | | | rs |] => //= Hfold [Hlen /Forall_fold_right Hall].
  have Hrs: rs = rs' ++ rs by simplify_list_eq. clear Hrs'.
  elim: ss {1 3 5}rs rs' Hlen Hrs Hfold Hall.
  { move => []//= ? ? ->. rewrite app_nil_r. naive_solver. }
  move => [??] ss IH [|[??]?]//= ? [?] ? Hfold /list.Forall_cons[[??]?]. simplify_eq/=.
  apply: IH; [done| | by apply: Hfold |done]. by simplify_list_eq.
Qed.

Global Instance simpl_and_bv_and_0xfff0000000000000 b :
  SimplAnd (bv_and b [BV{64} 0xfff0000000000000] = [BV{64} 0]) (λ T, bv_unsigned b < 2 ^ 52 ∧ T).
Proof.
  split; move => [Hb ?]; split => //.
  - bv_simplify.
    rewrite !bv_wrap_land.
    have -> : 0xfff0000000000000 = Z.ones 12 ≪ 52 by done.
    bitblast. bv_saturate.
    eapply Z_bounded_iff_bits_nonneg; [| |done|]; lia.
  - rewrite -(bv_wrap_small 64 (bv_unsigned b)) ?bv_wrap_land; [|bv_solve].
    eapply Z_bounded_iff_bits_nonneg; [lia | bv_solve|].
    move => i Hi. bv_simplify_hyp Hb. move: Hb.
    have -> : 0xfff0000000000000 = Z.ones 12 ≪ 52 by done.
    move => /Z.bits_inj_iff' Hb.
    move: (Hb i ltac:(lia)).
    rewrite !Z.land_spec Z.shiftl_spec ?Z.bits_0 ?Z_ones_spec; [|lia..].
    repeat case_bool_decide => //; lia.
Qed.

Global Instance simpl_and_bv_and_0xfff0000000000007 b :
  SimplAnd (bv_and b [BV{64} 0xfff0000000000007] = [BV{64} 0]) (λ T, bv_unsigned b < 2 ^ 52 ∧ bv_unsigned b `mod` 8 = 0 ∧ T).
Proof.
  split.
  - move => [Hb [Hmod ?]]; split => //.
    bv_simplify.
    rewrite !bv_wrap_land.
    have -> : 0xfff0000000000007 = Z.lor (Z.ones 12 ≪ 52) (Z.ones 3) by done.
    bitblast.
    + move: Hmod. rewrite -(Z.land_ones _ 3) //. move => /Z.bits_inj_iff' Hmod.
      move: (Hmod i ltac:(lia)).
      rewrite !Z.land_spec Z.ones_spec_low ?Z.bits_0; [|lia].
      by simplify_bool_eq.
    + bv_saturate.
      eapply Z_bounded_iff_bits_nonneg; [| |done|]; lia.
  - move => [Hb ?]. rewrite -{1}(bv_wrap_small 64 (bv_unsigned b)) ?bv_wrap_land; [|bv_solve].
    bv_simplify_hyp Hb. move: Hb.
    have -> : 0xfff0000000000007 = Z.lor (Z.ones 12 ≪ 52) (Z.ones 3) by done.
    move => /Z.bits_inj_iff' Hb.
    split_and! => //.
    + eapply Z_bounded_iff_bits_nonneg; [lia | bv_solve|].
      move => i Hi. move: (Hb i ltac:(lia)).
      rewrite !Z.land_spec Z.lor_spec Z.shiftl_spec ?Z.bits_0 ?Z_ones_spec; [|lia..].
      repeat case_bool_decide => //; lia.
    + rewrite -(Z.land_ones _ 3) //. bitblast.
      move: (Hb i ltac:(lia)).
      rewrite !Z.land_spec Z.lor_spec Z.shiftl_spec ?Z.bits_0 ?(Z.ones_spec_low 3); [|lia..].
      by simplify_bool_eq.
Qed.

(** * [normalize_instr_addr] *)

Definition normalize_instr_addr {Σ} (a1 : Z) (T : Z → iProp Σ) : iProp Σ :=
  ∃ a2, ⌜bv_wrap 64 a1 = bv_wrap 64 a2⌝ ∗ T a2.
Arguments normalize_instr_addr : simpl never.
Typeclasses Opaque normalize_instr_addr.

Program Definition normalize_instr_addr_hint {Σ} a1 a2 :
  (bv_wrap 64 a1 = bv_wrap 64 a2) →
  TacticHint (normalize_instr_addr (Σ:=Σ) a1) := λ H, {|
    tactic_hint_P T := T a2;
|}.
Next Obligation. unfold normalize_instr_addr. move => ??? -> ?. iIntros "?". iExists _. by iFrame. Qed.

Lemma normalize_instr_addr_add_tac a n r:
  bv_wrap 64 (a + bv_unsigned n) = r →
  bv_wrap 64 (bv_unsigned (bv_add (Z_to_bv 64 a) n)) = r.
Proof. move => <-. by rewrite bv_add_unsigned Z_to_bv_unsigned bv_wrap_bv_wrap // bv_wrap_add_idemp_l. Qed.

Ltac solve_normalize_instr_addr :=
  unfold normalize_instr_addr; unLET;
  try lazymatch goal with
  | |- bv_wrap _ ?a = _ => reduce_closed a
  end;
  try lazymatch goal with
  | |- bv_wrap _ (bv_unsigned (bv_add (Z_to_bv 64 _) _)) = _ => apply normalize_instr_addr_add_tac
  end;
  try lazymatch goal with
  | |- bv_wrap _ (_ + ?a) = _ => reduce_closed a
  end;
  exact: eq_refl.

Global Hint Extern 10 (TacticHint (normalize_instr_addr _)) =>
  eapply normalize_instr_addr_hint; solve_normalize_instr_addr : typeclass_instances.


(** * [normalize_bv_wrap] *)

Definition normalize_bv_wrap {Σ} (a1 : Z) (T : Z → iProp Σ) : iProp Σ :=
  ∃ a2, ⌜bv_wrap 64 a1 = bv_wrap 64 a2⌝ ∗ T a2.
Arguments normalize_bv_wrap : simpl never.
Typeclasses Opaque normalize_bv_wrap.

Program Definition normalize_bv_wrap_hint {Σ} a1 a2 :
  (∀ x, bv_wrap 64 a2 = x → block bv_wrap 64%N a1 = x) →
  TacticHint (normalize_bv_wrap (Σ:=Σ) a1) := λ H, {|
    tactic_hint_P T := T a2;
|}.
Next Obligation. unfold normalize_bv_wrap, block. move => ??? Heq ?. iIntros "?". iExists _. iFrame. iPureIntro. by apply: Heq. Qed.

Ltac solve_normalize_bv_wrap :=
  let H := fresh in move => ? H;
  bv_simplify;
  repeat match goal with | |- context [bv_wrap ?n ?x] => reduce_closed (bv_wrap n x) end;
  unfold block;
  bv_wrap_simplify_left;
  lazymatch goal with | |- bv_wrap _ ?z = _ => ring_simplify z end;
  apply H.

Global Hint Extern 10 (TacticHint (normalize_bv_wrap _)) =>
  eapply normalize_bv_wrap_hint; solve_normalize_bv_wrap : typeclass_instances.

(** * [compute_wp_exp] *)
Definition compute_wp_exp {Σ} `{!islaG Σ} (e : exp) (T : base_val → iProp Σ) : iProp Σ :=
  WPexp e {{ T }}.
Arguments compute_wp_exp : simpl never.
Typeclasses Opaque compute_wp_exp.

Fixpoint eval_exp' (e : exp) : option base_val :=
  match e with
  | Val x _ => Some x
  | Unop uo e' _ =>
    eval_exp' e' ≫= eval_unop uo
  | Binop uo e1 e2 _ =>
    v1 ← eval_exp' e1; v2 ← eval_exp' e2; eval_binop uo v1 v2
  | Manyop m es _ => vs ← mapM eval_exp' es; eval_manyop m vs
  | Ite e1 e2 e3 _ =>
    v1 ← eval_exp' e1; v2 ← eval_exp' e2; v3 ← eval_exp' e3;
    match v1 with
    | Val_Bool b =>
        match v2, v3 with
        | Val_Bits b2, Val_Bits b3 =>
            b3' ← bvn_to_bv b2.(bvn_n) b3;
            Some (Val_Bits (ite b b2.(bvn_val) b3'))
        | _, _ => Some (ite b v2 v3)
        end
    | _ => None
    end
  end.

Lemma eval_exp'_sound e v :
  eval_exp' e = Some v → eval_exp e = Some v.
Proof.
  move: e v. match goal with | |- ∀ e, @?P e => eapply (exp_ott_ind (λ es, Forall P es) P) end => //=.
  - move => ?? IH?? /bind_Some[?[/IH??]]. simplify_option_eq. naive_solver.
  - move => ?? IH1 ? IH2 ?? /bind_Some[?[/IH1 ? /bind_Some [?[/IH2 ?]]]]. simplify_option_eq. naive_solver.
  - move => ? /Forall_lookup IH ?? ? /bind_Some[?[/mapM_Some /Forall2_same_length_lookup??]].
    apply bind_Some. eexists _. split; [|done]. apply mapM_Some. apply/Forall2_same_length_lookup.
    naive_solver.
  - move => ? IH1 ? IH2 ? IH3 ?? /bind_Some[x1[/IH1 ? /bind_Some[x2 [/IH2 ? /bind_Some[x3 [/IH3 ? Hb]]]]]].
    simplify_option_eq. repeat case_match => //; unfold ite in *; simplify_eq => //.
    all: move: Hb => /bind_Some[x4 [Hb ?]]; simplify_eq => //.
    + by destruct bv5; simplify_eq/=.
    + unfold bvn_to_bv in *. case_decide as Hx => //. destruct Hx. simplify_eq/=.
      by destruct bv0.
  - move => *. by constructor.
Qed.


Program Definition compute_wp_exp_hint `{!islaG Σ} e v :
  (∀ x, Some v = x → eval_exp' e = x) →
  TacticHint (compute_wp_exp e) := λ H, {|
    tactic_hint_P T := T v;
|}.
Next Obligation.
  iIntros (??????) "HT". rewrite /compute_wp_exp wp_exp_unfold. iExists _. iFrame. iPureIntro.
  apply eval_exp'_sound. naive_solver.
Qed.

Ltac solve_compute_wp_exp :=
  let H := fresh in move => ? H;
  lazy [eval_exp' mapM mbind option_bind eval_unop eval_manyop eval_binop option_fmap option_map fmap mret option_ret foldl bvn_to_bv bv_to_bvn decide decide_rel N_eq_dec N.eq_dec N_rec N_rect bvn_n sumbool_rec sumbool_rect Pos.eq_dec positive_rect positive_rec eq_rect eq_ind_r eq_ind eq_sym bvn_val N.add N.sub Pos.add Pos.succ mguard option_guard Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask];
  lazymatch goal with | |- Some _ = _ => idtac | |- ?G => idtac "solve_copmute_wp_exp failed:" G; fail end;
  try lazymatch goal with | |- Some (Val_Bits (BVN _ ?b)) = ?e => change (Some (Val_Bits (bv_to_bvn b)) = e) end;
  autorewrite with bv_simplify;
  apply H.

Global Hint Extern 10 (TacticHint (compute_wp_exp _)) =>
  eapply compute_wp_exp_hint; solve_compute_wp_exp : typeclass_instances.

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac normalize_tac ::=
  autorewrite with isla_coq_rewrite; exact: eq_refl.
(* Ltac normalize_tac ::= normalize_autorewrite. *)

Ltac bv_solve_unfold_tac ::=
  unfold byte, addr in *.

Ltac solve_protected_eq_unfold_tac ::=
  reduce_closed_N.

(* injection on bitvectors sometimes creates weird matches, so we disable it. *)
Ltac check_injection_tac ::=
  lazymatch goal with
  | |- @eq (bv _) _ _ → _ => fail
  | |- _ => idtac
  end.

Ltac prepare_sidecond :=
  li_unshelve_sidecond; unLET; normalize_and_simpl_goal => //=.

Definition let_bind_hint {A B} (x : A) (f : A → B) : B :=
  f x.

Inductive instr_kind {Σ} : Type :=
| IKInstr (ins : option (list trc)) | IKPre (l : bool) (P : iProp Σ).
Definition FindInstrKind {Σ} `{!Arch} `{!islaG Σ} `{!threadG} (a : Z) (l : bool) := {|
  fic_A := @instr_kind Σ;
  fic_Prop ik :=
    match ik with
    | IKInstr ins => instr a ins
    | IKPre l' P => instr_pre' l' a P
    end
|}.
Typeclasses Opaque FindInstrKind.

Inductive reg_mapsto_kind : Type :=
| RKMapsTo (v : valu) | RKCol (regs : list (reg_kind * valu_shape)).
Definition FindRegMapsTo {Σ} `{!islaG Σ} `{!threadG} (r : string) := {|
  fic_A := reg_mapsto_kind;
  fic_Prop rk :=
  match rk with
  | RKMapsTo v => (r ↦ᵣ v)%I
  | RKCol regs => reg_col regs
  end
|}.
Typeclasses Opaque FindRegMapsTo.
Definition FindStructRegMapsTo {Σ} `{!islaG Σ} `{!threadG} (r f : string) := {|
  fic_A := reg_mapsto_kind;
  fic_Prop rk :=
  match rk with
  | RKMapsTo v => (r # f ↦ᵣ v)%I
  | RKCol regs => reg_col regs
  end
|}.
Typeclasses Opaque FindStructRegMapsTo.

Inductive mem_mapsto_kind : Type :=
| MKMapsTo (n : N) (v : bv n)
| MKArray (n : N) (a : Z) (l : list (bv n))
| MKUninit (a : Z) (n : Z)
| MKMMIO (a : Z) (l : Z).
Definition FindMemMapsTo {Σ} `{!islaG Σ} `{!threadG} (a : Z) := {|
  fic_A := mem_mapsto_kind;
  fic_Prop mk :=
  match mk with
  | MKMapsTo _ v => (a ↦ₘ v)%I
  | MKArray _ a' l => (a' ↦ₘ∗ l)%I
  | MKUninit a' n => (a' ↦ₘ? n)%I
  | MKMMIO a' l => mmio_range a' l
  end
|}.

Section instances.
  Context `{!Arch} `{!islaG Σ} `{!threadG}.

  Global Instance instr_intro_pers i a : IntroPersistent (instr a i) (instr a i).
  Proof. constructor. iIntros "#$". Qed.

  Global Instance mmio_range_intro_pers a l : IntroPersistent (mmio_range a l) (mmio_range a l).
  Proof. constructor. iIntros "#$". Qed.

  (* If there is no later in the goal (i.e. the second parameter to FindInstrKind is false),
     we should only find instr_pre with false in the context. Otherwise, we can find an
     arbitrary instr_pre. *)
  Lemma find_in_context_instr_kind_pre_false a T:
    (∃ P, instr_pre' false a P ∗ T (IKPre false P)) -∗
    find_in_context (FindInstrKind a false) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_instr_kind_pre_false_inst a :
    FindInContext (FindInstrKind a false) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_instr_kind_pre_false a T).

  Lemma find_in_context_instr_kind_pre_true a T:
    (∃ l P, instr_pre' l a P ∗ T (IKPre l P)) -∗
    find_in_context (FindInstrKind a true) T.
  Proof. iDestruct 1 as (??) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_instr_kind_pre_true_inst a :
    FindInContext (FindInstrKind a true) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_instr_kind_pre_true a T).

  Lemma find_in_context_instr_kind_instr a T l:
    (∃ ins, instr a ins ∗ T (IKInstr ins)) -∗
    find_in_context (FindInstrKind a l) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_instr_kind_instr_inst a l:
    FindInContext (FindInstrKind a l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_instr_kind_instr a T l).

  Inductive FICInstrSemantic : Set :=.
  Global Instance find_in_context_instr_pre_semantic_false_inst a :
    FindInContext (FindInstrKind a false) FICInstrSemantic | 100 :=
    λ T, i2p (find_in_context_instr_kind_pre_false a T).
  Global Instance find_in_context_instr_pre_semantic_true_inst a :
    FindInContext (FindInstrKind a true) FICInstrSemantic | 100 :=
    λ T, i2p (find_in_context_instr_kind_pre_true a T).

  Lemma tac_instr_pre_eq l1 l2 a1 a2 P1 P2:
    a1 = a2 →
    FindHypEqual FICInstrSemantic (instr_pre' l1 a1 P1) (instr_pre' l2 a2 P2) (instr_pre' l2 a1 P2).
  Proof. by move => ->. Qed.

  Global Instance find_in_context_instr_semantic_inst a l:
    FindInContext (FindInstrKind a l) FICInstrSemantic | 110 :=
    λ T, i2p (find_in_context_instr_kind_instr a T l).

  Lemma tac_instr_eq a1 a2 ins1 ins2:
    a1 = a2 →
    FindHypEqual FICInstrSemantic (instr a1 ins1) (instr a2 ins2) (instr a1 ins2).
  Proof. by move => ->. Qed.

  Global Instance mem_related a n (v : bv n) : RelatedTo (a ↦ₘ v) := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Global Instance mem_array_related a n (l : list (bv n)) : RelatedTo (a ↦ₘ∗ l) := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Global Instance mem_uninit_related a n : RelatedTo (a ↦ₘ? n) := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Lemma find_in_context_mem_mapsto_id a T:
    (∃ n (v : bv n), a ↦ₘ v ∗ T (MKMapsTo n v)) -∗
    find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (? v) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_mapsto_id_inst a :
    FindInContext (FindMemMapsTo a) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_mem_mapsto_id a T).

  Inductive FICMemMapstoSemantic (a : Z) : Set :=.
  Global Instance find_in_context_mem_mapsto_semantic_inst a :
    FindInContext (FindMemMapsTo a) (FICMemMapstoSemantic a) | 10 :=
    λ T, i2p (find_in_context_mem_mapsto_id a T).

  Lemma tac_mem_mapsto_eq l1 l' n (v1 v2 : bv n) l2:
    l1 = l2 →
    FindHypEqual (FICMemMapstoSemantic l') (l1 ↦ₘ v1) (l2 ↦ₘ v2) (l1 ↦ₘ v2).
  Proof. by move => ->. Qed.

  Lemma find_in_context_mem_mapsto_array a T:
    (∃ n a' l, a' ↦ₘ∗ l ∗ T (MKArray n a' l)) -∗
    find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (n a' l) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_mapsto_array_inst a :
    FindInContext (FindMemMapsTo a) (FICMemMapstoSemantic a) | 20 :=
    λ T, i2p (find_in_context_mem_mapsto_array a T).

  Lemma tac_mem_mapsto_array_eq a n a1 a2 (l1 l2 : list (bv n)):
    a1 ≤ a < a1 + length l1 * Z.of_N (n `div` 8)%N
      ∨ a1 = a →
    FindHypEqual (FICMemMapstoSemantic a) (a1 ↦ₘ∗ l1) (a2 ↦ₘ∗ l2) (a2 ↦ₘ∗ l2).
  Proof. done. Qed.

  Lemma find_in_context_mem_mapsto_uninit a T:
    (∃ a' n', a' ↦ₘ? n' ∗ T (MKUninit a' n')) -∗
    find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (a' n') "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_mapsto_uninit_inst a :
    FindInContext (FindMemMapsTo a) (FICMemMapstoSemantic a) | 30 :=
    λ T, i2p (find_in_context_mem_mapsto_uninit a T).

  Lemma tac_mem_mapsto_uninit_eq a a1 a2 n1 n2:
    a1 ≤ a < a1 + n1 ∨ a1 = a →
    FindHypEqual (FICMemMapstoSemantic a) (a1 ↦ₘ? n1) (a2 ↦ₘ? n2) (a2 ↦ₘ? n2).
  Proof. done. Qed.

  Lemma find_in_context_mem_mapsto_mmio a T:
    (∃ a' l, mmio_range a' l ∗ T (MKMMIO a' l)) -∗
    find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (a' l) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_mem_mapsto_mmio_semantic_inst a :
  FindInContext (FindMemMapsTo a) (FICMemMapstoSemantic a) | 40 :=
  λ T, i2p (find_in_context_mem_mapsto_mmio a T).

  Lemma tac_mem_mapsto_mmio a a1 a2 l1 l2:
    a1 ≤ a ≤ a1 + l1 →
    FindHypEqual (FICMemMapstoSemantic a) (mmio_range a1 l1) (mmio_range a2 l2) (mmio_range a2 l2).
  Proof. done. Qed.

  Global Instance reg_related r v : RelatedTo (r ↦ᵣ v) := {|
    rt_fic := FindRegMapsTo r;
  |}.

  Global Instance struct_reg_related r f v : RelatedTo (r # f ↦ᵣ v) := {|
    rt_fic := FindStructRegMapsTo r f;
  |}.

  Global Instance reg_pred_related r P : RelatedTo (r ↦ᵣ: P) := {|
    rt_fic := FindRegMapsTo r;
  |}.
  Global Instance struct_reg_pred_related r f P : RelatedTo (r # f ↦ᵣ: P) := {|
    rt_fic := FindStructRegMapsTo r f;
  |}.

  Lemma find_in_context_reg_mapsto r T:
    (∃ v, r ↦ᵣ v ∗ T (RKMapsTo v)) -∗
    find_in_context (FindRegMapsTo r) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_reg_mapsto_inst r :
    FindInContext (FindRegMapsTo r) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_reg_mapsto r T).

  Lemma find_in_context_reg_mapsto_col r T:
    (∃ regs, reg_col regs ∗ T (RKCol regs)) -∗
    find_in_context (FindRegMapsTo r) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Inductive FICRegMapstoSemantic (r : string) : Set :=.
  Global Instance find_in_context_reg_mapsto_col_inst r :
    FindInContext (FindRegMapsTo r) (FICRegMapstoSemantic r) | 10 :=
    λ T, i2p (find_in_context_reg_mapsto_col r T).

  Lemma tac_reg_mapsto_reg_col r regs1 regs2:
    is_Some (list_find_idx (λ x, x.1 = KindReg r) regs1) →
    FindHypEqual (FICRegMapstoSemantic r) (reg_col regs1) (reg_col regs2) (reg_col regs2) .
  Proof. done. Qed.

  Lemma find_in_context_struct_reg_mapsto r f T:
    (∃ v, r # f ↦ᵣ v ∗ T (RKMapsTo v)) -∗
    find_in_context (FindStructRegMapsTo r f) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Global Instance find_in_context_struct_reg_mapsto_inst r f :
    FindInContext (FindStructRegMapsTo r f) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_struct_reg_mapsto r f T).

  Lemma find_in_context_struct_reg_mapsto_col r f T:
    (∃ regs, reg_col regs ∗ T (RKCol regs)) -∗
    find_in_context (FindStructRegMapsTo r f) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Inductive FICStructRegMapstoSemantic (r f : string) : Set :=.
  Global Instance find_in_context_struct_reg_mapsto_col_inst r f:
    FindInContext (FindStructRegMapsTo r f) (FICStructRegMapstoSemantic r f) | 10 :=
    λ T, i2p (find_in_context_struct_reg_mapsto_col r f T).

  Lemma tac_struct_reg_mapsto_reg_col r f regs1 regs2:
    is_Some (list_find_idx (λ x, x.1 = KindField r f ∨ x.1 = KindReg r) regs1) →
    FindHypEqual (FICStructRegMapstoSemantic r f) (reg_col regs1) (reg_col regs2) (reg_col regs2) .
  Proof. done. Qed.

  Global Instance instr_related a i : RelatedTo (instr a i) := {|
    rt_fic := FindDirect (λ i, instr a i)%I;
  |}.

  Global Instance instr_pre'_related b a P : RelatedTo (instr_pre' b a P) := {|
    rt_fic := FindInstrKind a b;
  |}.

  Global Instance spec_trace_related κs : RelatedTo (spec_trace κs) := {|
    rt_fic := FindDirect (λ κs, spec_trace κs)%I;
  |}.

  Lemma subsume_reg r v1 v2 G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (r ↦ᵣ v1) (r ↦ᵣ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_reg_inst r v1 v2 :
    Subsume (r ↦ᵣ v1) (r ↦ᵣ v2) :=
    λ G, i2p (subsume_reg r v1 v2 G).

  Lemma subsume_struct_reg r f v1 v2 G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (r # f ↦ᵣ v1) (r # f ↦ᵣ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_struct_reg_inst r f v1 v2 :
    Subsume (r # f ↦ᵣ v1) (r # f ↦ᵣ v2) :=
    λ G, i2p (subsume_struct_reg r f v1 v2 G).

  Lemma subsume_regcol_reg regs r v G:
    (tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
      ∀ vr, ⌜regs !! i = Some vr⌝ -∗ reg_col (delete i regs) -∗ ∀ v', ⌜valu_has_shape v' vr.2⌝ -∗ ⌜v = v'⌝ ∗ G)) -∗
    subsume (reg_col regs) (r ↦ᵣ v) G.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (i [[??][?[??]]]%list_find_idx_Some) "HG"; simplify_eq/=. iIntros "Hr".
    rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
    iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
    iDestruct ("HG" with "[//] Hregs") as "HG"; simplify_eq/=.
    by iDestruct ("HG" with "[//]") as "[-> $]".
  Qed.
  Global Instance subsume_regcol_reg_inst regs r v:
    Subsume (reg_col regs) (r ↦ᵣ v) :=
    λ G, i2p (subsume_regcol_reg regs r v G).

  Lemma subsume_struct_regcol_reg regs r f v G:
    (tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f)) regs) (λ i,
      (∀ vr, ⌜regs !! i = Some vr⌝ -∗ reg_col (delete i regs) -∗ ∀ v', ⌜valu_has_shape v' vr.2⌝ -∗ ⌜v = v'⌝ ∗ G))) -∗
    subsume (reg_col regs) (r # f ↦ᵣ v) G.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (i [[??][?[??]]]%list_find_idx_Some) "HG"; simplify_eq/=. iIntros "Hr".
    rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
    iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
    iDestruct ("HG" with "[//] Hregs") as "HG"; simplify_eq/=.
    by iDestruct ("HG" with "[//]") as "[-> $]".
  Qed.
  Global Instance subsume_struct_regcol_reg_inst regs r f v:
    Subsume (reg_col regs) (r # f ↦ᵣ v) :=
    λ G, i2p (subsume_struct_regcol_reg regs r f v G).

  Lemma subsume_reg_reg_pred r v P G:
    P v ∗ G -∗
    subsume (r ↦ᵣ v) (r ↦ᵣ: P) G.
  Proof. iIntros "[? $] ?". rewrite reg_mapsto_pred_eq. iExists _. iFrame. Qed.
  Global Instance subsume_reg_reg_pred_inst r v P:
    Subsume (r ↦ᵣ v) (r ↦ᵣ: P) :=
      λ G, i2p (subsume_reg_reg_pred r v P G).

  Lemma subsume_struct_reg_reg_pred r f v P G:
    P v ∗ G -∗
      subsume (r # f ↦ᵣ v) (r # f ↦ᵣ: P) G.
  Proof. iIntros "[? $] ?". rewrite struct_reg_mapsto_pred_eq. iExists _. iFrame. Qed.
  Global Instance subsume_struct_reg_reg_pred_inst r f v P:
    Subsume (r # f ↦ᵣ v) (r # f ↦ᵣ: P) :=
    λ G, i2p (subsume_struct_reg_reg_pred r f v P G).

  Lemma subsume_regcol_reg_pred regs r P G:
    (tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
      (∀ vr v', ⌜regs !! i = Some vr⌝ -∗ ⌜valu_has_shape v' vr.2⌝ -∗
         reg_col (delete i regs) -∗ P v' ∗ G))) -∗
    subsume (reg_col regs) (r ↦ᵣ: P) G.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (i [[??][?[??]]]%list_find_idx_Some) "HG"; simplify_eq/=. iIntros "Hr".
    rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
    iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
    iDestruct ("HG" with "[//] [//] Hregs") as "[? $]".
    rewrite reg_mapsto_pred_eq. iExists _. iFrame.
  Qed.
  Global Instance subsume_regcol_reg_pred_inst regs r P:
    Subsume (reg_col regs) (r ↦ᵣ: P) :=
    λ G, i2p (subsume_regcol_reg_pred regs r P G).

  Lemma subsume_struct_regcol_reg_pred regs r f P G:
    (tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f)) regs) (λ i,
      (∀ vr v', ⌜regs !! i = Some vr⌝ -∗ ⌜valu_has_shape v' vr.2⌝ -∗
         reg_col (delete i regs) -∗ P v' ∗ G))) -∗
    subsume (reg_col regs) (r # f ↦ᵣ: P) G.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (i [[??][?[??]]]%list_find_idx_Some) "HG"; simplify_eq/=. iIntros "Hr".
    rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
    iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
    iDestruct ("HG" with "[//] [//] Hregs") as "[? $]".
    rewrite struct_reg_mapsto_pred_eq. iExists _. iFrame.
  Qed.
  Global Instance subsume_struct_regcol_reg_pred_inst regs r f P:
    Subsume (reg_col regs) (r # f ↦ᵣ: P) :=
    λ G, i2p (subsume_struct_regcol_reg_pred regs r f P G).

  Lemma reg_mapsto_pred_intro r P :
    find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v => P v
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
           (∀ vr v', ⌜regs !! i = Some vr⌝ -∗ ⌜valu_has_shape v' vr.2⌝ -∗
             reg_col (delete i regs) -∗ P v'))
      end) -∗
    r ↦ᵣ: P.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - eauto with iFrame.
    - iDestruct "Hwp" as (i [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
      iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
      iExists _. iFrame. iApply ("Hwp" with "[//] [//] Hregs").
  Qed.

  Lemma struct_reg_mapsto_pred_intro r f P :
    find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v => P v
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f)) regs) (λ i,
           (∀ vr v', ⌜regs !! i = Some vr⌝ -∗ ⌜valu_has_shape v' vr.2⌝ -∗
             reg_col (delete i regs) -∗ P v'))
      end) -∗
    r # f ↦ᵣ: P.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    rewrite struct_reg_mapsto_pred_eq /struct_reg_mapsto_pred_def.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - eauto with iFrame.
    - iDestruct "Hwp" as (i [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
      iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
      iExists _. iFrame. iApply ("Hwp" with "[//] [//] Hregs").
  Qed.

  Lemma simpl_hyp_reg_pred r P G:
    (∀ v, r ↦ᵣ v -∗ P v -∗ G) -∗
    simplify_hyp (r ↦ᵣ: P) G.
  Proof.
    rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iIntros "HG [%v [? ?]]". by iApply ("HG" with "[$]").
  Qed.
  Global Instance simpl_hyp_reg_pred_inst r P:
    SimplifyHyp (r ↦ᵣ: P) (Some 0%N) :=
    λ G, i2p (simpl_hyp_reg_pred r P G).

  Lemma simpl_hyp_struct_reg_pred r f P G:
    (∀ v, r # f ↦ᵣ v -∗ P v -∗ G) -∗
    simplify_hyp (r # f ↦ᵣ: P) G.
  Proof.
    rewrite struct_reg_mapsto_pred_eq /struct_reg_mapsto_pred_def.
    iIntros "HG [%v [? ?]]". by iApply ("HG" with "[$]").
  Qed.
  Global Instance simpl_hyp_struct_reg_pred_inst r f P:
    SimplifyHyp (r # f ↦ᵣ: P) (Some 0%N) :=
    λ G, i2p (simpl_hyp_struct_reg_pred r f P G).

  Lemma subsume_instr a i1 i2 G:
    ⌜i1 = i2⌝ ∗ G -∗
    subsume (instr a i1) (instr a i2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_instr_inst a i1 i2 :
    Subsume (instr a i1) (instr a i2) :=
    λ G, i2p (subsume_instr a i1 i2 G).

  Lemma subsume_instr_pre' a b1 b2 P1 P2 G:
    ⌜b1 = b2⌝ ∗ ⌜P1 = P2⌝ ∗ G -∗
    subsume (instr_pre' b1 a P1) (instr_pre' b2 a P2) G.
  Proof. iDestruct 1 as (-> ->) "$". iIntros "$". Qed.
  Global Instance subsume_instr_pre'_inst a b1 b2 P1 P2 :
    Subsume (instr_pre' b1 a P1) (instr_pre' b2 a P2) :=
    λ G, i2p (subsume_instr_pre' a b1 b2 P1 P2 G).

  Lemma subsume_spec_trace_protected Pκs1 Pκs2 G `{!IsProtected Pκs2}:
    ⌜Pκs1 = Pκs2⌝ ∗ G -∗
    subsume (spec_trace Pκs1) (spec_trace Pκs2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_spec_trace_protected_inst Pκs1 Pκs2 `{!IsProtected Pκs2}:
    Subsume (spec_trace Pκs1) (spec_trace Pκs2) | 10 :=
    λ G, i2p (subsume_spec_trace_protected Pκs1 Pκs2 G).

  Lemma subsume_spec_trace Pκs1 Pκs2 G:
    ⌜Pκs2 ⊆ Pκs1⌝ ∗ G -∗
    subsume (spec_trace Pκs1) (spec_trace Pκs2) G.
  Proof. iDestruct 1 as (?) "$". by iApply spec_trace_mono. Qed.
  Global Instance subsume_spec_trace_inst κs1 κs2 :
    Subsume (spec_trace κs1) (spec_trace κs2) | 50 :=
    λ G, i2p (subsume_spec_trace κs1 κs2 G).

  Lemma subsume_mem a n (v1 v2 : bv n) G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (a ↦ₘ v1) (a ↦ₘ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_mem_inst a n (v1 v2 : bv n) :
    Subsume (a ↦ₘ v1) (a ↦ₘ v2) :=
    λ G, i2p (subsume_mem a n v1 v2 G).

  Lemma subsume_mem_array a1 a2 n (l1 l2 : list (bv n)) G:
    ⌜a1 = a2⌝ ∗ ⌜l1 = l2⌝ ∗ G -∗
    subsume (a1 ↦ₘ∗ l1) (a2 ↦ₘ∗ l2) G.
  Proof. iDestruct 1 as (-> ->) "$". iIntros "$". Qed.
  Global Instance subsume_mem_array_inst a1 a2 n (l1 l2 : list (bv n)) :
    Subsume (a1 ↦ₘ∗ l1) (a2 ↦ₘ∗ l2) :=
    λ G, i2p (subsume_mem_array a1 a2 n l1 l2 G).

  (* This handles the case where the goal is fully contained in the hypthesis. I.e.
     |------ hyp ------|
          |-- goal --|
  *)
  Lemma subsume_mem_uninit_mem_uninit a1 a2 n1 n2 G
        `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 + n2 ≤ a1 + n1)}:
    (tactic_hint (normalize_bv_wrap (a2 - a1)) (λ m1, ⌜0 ≤ m1 < 2 ^ 64⌝ ∗
     tactic_hint (normalize_bv_wrap (n1 - n2 - m1)) (λ m2, ⌜0 ≤ m2 < 2 ^ 64 ∧ n1 < 2 ^ 64⌝ ∗ (
      a1 ↦ₘ? m1 -∗
     (a2 + n2) ↦ₘ? m2 -∗ G)))) -∗
     subsume (a1 ↦ₘ? n1) (a2 ↦ₘ? n2) G.
  Proof.
    unfold BvSolve, normalize_bv_wrap, tactic_hint in *. iIntros "HG Ha".
    iDestruct "HG" as "(%m1&%Hm1&%&%m2&%Hm2&%&HG)".
    iDestruct (mem_mapsto_uninit_split m1 with "Ha") as "[? Ha]"; [bv_solve|].
    iDestruct (mem_mapsto_uninit_split n2 with "Ha") as "[? Ha]"; [bv_solve|].
    have -> : a1 + m1 = a2 by bv_solve.
    have -> : (n1 - m1 - n2) = m2 by bv_solve.
    iFrame. iApply ("HG" with "[$] [$]").
  Qed.
  Global Instance subsume_mem_uninit_mem_uninit_inst a1 a2 n1 n2
         `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 + n2 ≤ a1 + n1)}:
    Subsume (a1 ↦ₘ? n1) (a2 ↦ₘ? n2) :=
    λ G, i2p (subsume_mem_uninit_mem_uninit a1 a2 n1 n2 G).

  (* This handles the case where the kypothesis does not fully containe the goal. I.e.
     |--- hyp ---|
          |-- goal --|
   *)
  (* This rule breaks if one of the uninit spans 2^64 bytes but that seems quite rare. *)
  Lemma subsume_mem_uninit_mem_uninit2 a1 a2 n1 n2 G
        `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 ≤ a1 + n1 ∧ a1 + n1 ≤ a2 + n2)}:
    (tactic_hint (normalize_bv_wrap (a2 - a1)) (λ m1, ⌜0 ≤ m1 < 2 ^ 64⌝ ∗
     tactic_hint (normalize_bv_wrap (n2 - (n1 - m1))) (λ m2, ⌜0 ≤ m2 < 2 ^ 64⌝ ∗
     tactic_hint (normalize_bv_wrap (a2 + n1 - m1)) (λ m3, ⌜a2 + n2 < 2 ^ 64 ∧ m3 + m2 < 2 ^ 64⌝ ∗ (
     a1 ↦ₘ? m1 -∗
     m3 ↦ₘ? m2 ∗ G))))) -∗
     subsume (a1 ↦ₘ? n1) (a2 ↦ₘ? n2) G.
  Proof.
    unfold BvSolve, normalize_bv_wrap, tactic_hint in *. iIntros "HG Ha".
    iDestruct "HG" as "(%m1&%Hm1&%&%m2&%Hm2&%&%m3&%Hm3&%&HG)".
    iDestruct (mem_mapsto_uninit_in_range with "Ha") as %?.
    iDestruct (mem_mapsto_uninit_split m1 with "Ha") as "[? Ha]"; [bv_solve|].
    iDestruct ("HG" with "[$]") as "[H1 $]".
    have -> : a1 + m1 = a2 by bv_solve.
    iApply (mem_mapsto_uninit_combine with "Ha"); [bv_solve|].
    iDestruct (mem_mapsto_uninit_in_range with "H1") as %?.
    have -> : (a2 + (n1 - m1)) = m3 by bv_solve.
    by have -> : (n2 - (n1 - m1)) = m2 by bv_solve.
  Qed.
  Global Instance subsume_mem_uninit_mem_uninit2_inst a1 a2 n1 n2
        `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 ≤ a1 + n1 ∧ a1 + n1 ≤ a2 + n2)}:
    Subsume (a1 ↦ₘ? n1) (a2 ↦ₘ? n2) :=
    λ G, i2p (subsume_mem_uninit_mem_uninit2 a1 a2 n1 n2 G).

  (* This rule breaks if one of the uninit spans 2^64 bytes but that seems quite rare. *)
  Lemma subsume_mem_mapsto_mem_uninit a1 a2 n (b : bv n) n2 G:
    (⌜a1 = a2⌝ ∗ ⌜Z.of_N (n `div` 8) ≤ n2⌝ ∗
    (a2 + (Z.of_N (n `div` 8))) ↦ₘ? (n2 - (Z.of_N (n `div` 8))) ∗ G) -∗
     subsume (a1 ↦ₘ b) (a2 ↦ₘ? n2) G.
  Proof.
    iIntros "[-> [% [Ha2 $]]] Ha".
    iDestruct (mem_mapsto_n_mult_8 with "Ha") as %[n' ?]; subst.
    iDestruct (mem_mapsto_mapsto_to_uninit with "Ha") as "Ha".
    by iApply (mem_mapsto_uninit_combine with "Ha"); [bv_solve|].
  Qed.
  Global Instance subsume_mem_mapsto_mem_uninit_inst a1 a2 n (b : bv n) n2:
    Subsume (a1 ↦ₘ b) (a2 ↦ₘ? n2) :=
    λ G, i2p (subsume_mem_mapsto_mem_uninit a1 a2 n b n2 G).

  Lemma simpl_hyp_uninit_0 a n G:
    G -∗
    simplify_hyp (a ↦ₘ? n) G.
  Proof. by iIntros "$ ?". Qed.
  Global Instance simpl_hyp_uninit_0_inst a n `{!BvSolve (n = 0)}:
    SimplifyHyp (a ↦ₘ? n) (Some 0%N) :=
    λ G, i2p (simpl_hyp_uninit_0 a n G).

  Lemma simpl_goal_uninit_0 a n G `{!BvSolve (n = 0)}:
    G ⌜0 ≤ a ≤ 2 ^ 64⌝ -∗
    simplify_goal (a ↦ₘ? n) G.
  Proof.
    unfold BvSolve in *. subst. iIntros "?". iExists _.
    iFrame. iIntros (?). by rewrite mem_mapsto_uninit_0.
  Qed.
  Global Instance simpl_goal_uninit_0_inst a n `{!BvSolve (n = 0)}:
    SimplifyGoal (a ↦ₘ? n) (Some 0%N) :=
    λ G, i2p (simpl_goal_uninit_0 a n G).

  Lemma simpl_goal_reg_col_nil T:
    (T True) -∗
    simplify_goal (reg_col []) T.
  Proof.
    iIntros "?". iExists _. iFrame. by rewrite reg_col_nil.
  Qed.
  Global Instance simpl_goal_reg_col_nil_inst :
    SimplifyGoal (reg_col []) (Some 100%N) :=
    λ T, i2p (simpl_goal_reg_col_nil T).

  Lemma simpl_goal_reg_col_cons r col s T:
    (T (match r with
        | KindReg r => r ↦ᵣ: (λ v, ⌜valu_has_shape v s⌝)
        | KindField r f => r # f ↦ᵣ: (λ v, ⌜valu_has_shape v s⌝)
        end ∗ reg_col col)) -∗
           simplify_goal (reg_col ((r, s)::col)) T.
  Proof.
    iIntros "?". iExists _. iFrame.
    rewrite reg_col_cons. iIntros "[Hr $]". case_match.
    - rewrite reg_mapsto_pred_eq. iDestruct "Hr" as (?) "[? %]". eauto with iFrame.
    - rewrite struct_reg_mapsto_pred_eq. iDestruct "Hr" as (?) "[? %]". eauto with iFrame.
  Qed.
  Global Instance simpl_goal_reg_col_cons_inst r col s :
    SimplifyGoal (reg_col ((r, s)::col)) (Some 100%N) :=
    λ T, i2p (simpl_goal_reg_col_cons r col s T).

  Lemma li_wp_next_instr:
    (∃ (nPC newPC : addr),
     arch_pc_reg ↦ᵣ RVal_Bits nPC ∗
     tactic_hint (normalize_instr_addr (bv_unsigned nPC)) (λ normPC,
     ⌜newPC = Z_to_bv 64 normPC⌝ ∗
     find_in_context (FindInstrKind normPC true) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, arch_pc_reg ↦ᵣ RVal_Bits newPC -∗ WPasm t
     | IKInstr (None) =>
       ∃ Pκs, spec_trace Pκs ∗ ⌜scons (SInstrTrap newPC) snil ⊆ Pκs⌝ ∗ True
     | IKPre l P => P
     end
    ))) -∗
    WPasm [].
  Proof.
    unfold normalize_instr_addr. iDestruct 1 as (??) "(HPC&%normPC&%Hnorm&->&Hwp)".
    have ? := bv_unsigned_in_range _ nPC.
    iDestruct "Hwp" as (ins) "[Hi Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iDestruct (instr_addr_in_range with "Hi") as %?.
      rewrite !bv_wrap_small // in Hnorm. subst.
      iApply (wp_next_instr with "HPC Hi [Hl]") => //.
      iIntros "!>" (i Hi) "?". rewrite Z_to_bv_bv_unsigned.
      iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
      iApply ("Hwp" with "[$]").
    - iDestruct "Hwp" as (?) "(?&%Hscons&?)".
      iDestruct (instr_addr_in_range with "Hi") as %?.
      rewrite !bv_wrap_small // in Hnorm. subst.
      rewrite Z_to_bv_bv_unsigned in Hscons.
      iApply (wp_next_instr_extern with "HPC [$] [$]") => //.
      spec_solver.
    - iApply (wp_next_instr_pre with "[$] [Hi] Hwp").
      iApply (instr_pre_wand with "Hi"); [by erewrite implb_same| |by iIntros "$"].
      by rewrite -Hnorm bv_wrap_small.
  Qed.

  Lemma li_instr_pre l a P:
    (∃ newPC,
     tactic_hint (normalize_instr_addr a) (λ normPC,
     ⌜newPC = Z_to_bv 64 normPC⌝ ∗
     find_in_context (FindInstrKind normPC l) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, P -∗ arch_pc_reg ↦ᵣ RVal_Bits newPC -∗ WPasm t
     | IKInstr None =>
       P -∗ ∃ Pκs, spec_trace Pκs ∗ ⌜scons (SInstrTrap newPC) snil ⊆ Pκs⌝ ∗ True
     | IKPre l' Q => ⌜implb l' l⌝ ∗ (P -∗ Q)
     end
    ))) -∗
    instr_pre' l a P.
  Proof.
    unfold normalize_instr_addr.  iDestruct 1 as (? normPC Hnorm -> ins) "[Hinstr Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iDestruct (instr_addr_in_range with "Hinstr") as %?.
      rewrite (bv_wrap_small _ normPC) // in Hnorm. subst.
      iApply (instr_pre_wand with "[-]"); [by erewrite implb_same| | | iIntros "HP"; iApply "HP"].
      2: iApply (instr_pre_intro_Some with "[$]"); [done..|].
      { by rewrite bv_wrap_bv_wrap. }
      iIntros (i Hi) "??".
      iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
      iApply ("Hwp" with "[$] [$]").
    - iDestruct (instr_addr_in_range with "Hinstr") as %?.
      rewrite (bv_wrap_small _ normPC) // in Hnorm. subst.
      iApply (instr_pre_wand with "[-]"); [by erewrite implb_same| | | iIntros "HP"; iApply "HP"].
      2: iApply (instr_pre_intro_None with "[$]"); [done..|].
      { by rewrite bv_wrap_bv_wrap. }
      iIntros "HP". iDestruct ("Hwp" with "HP") as (?) "[? [% _]]".
      iExists _. iFrame. iPureIntro. spec_solver.
    - iDestruct "Hwp" as (?) "Hwand".
      by iApply (instr_pre_wand with "Hinstr").
  Qed.

  Lemma li_wp_read_reg r v ann es :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜v = v'⌝ -∗ r ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
           (reg_col regs -∗ WPasm es))
      end)) -∗
    WPasm (ReadReg r [] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_read_reg with "Hr").
    - iDestruct "Hwp" as (? [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|] => /=.
      iApply (wp_read_reg with "Hr"). iIntros "% Hr". iApply "Hwp". iApply "Hregs".
      iExists _. by iFrame.
  Qed.

  Lemma li_wp_read_reg_struct r f v ann es :
    (∃ vread, ⌜read_accessor [Field f] v = Some vread⌝ ∗
     (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜vread = v'⌝ -∗ r # f ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f ∨ (x.1 = KindReg r ∧ is_Some
             (match x.2 with
              | ExactShape (RegVal_Struct rs) => list_find_idx (λ y, y.1 = f) rs
              | StructShape ss => list_find_idx (λ y, y.1 = f) ss
              | _ => None
              end)))%type) regs) (λ i,
               (reg_col regs -∗ WPasm es))
      end))) -∗
    WPasm (ReadReg r [Field f] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (???) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_read_reg_struct with "Hr").
    - iDestruct "Hwp" as (? [[? s][?[Hor ?]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [%Hvact Hr]] Hregs]"; [done|] => /=.
      case: Hor => [?|[?[i]]]; simplify_eq.
      + iApply (wp_read_reg_struct with "Hr"); [done|]. iIntros "% Hr". iApply "Hwp". iApply "Hregs".
        iExists _. by iFrame.
      + destruct s as [[]| | | |] => // Hidx; move: (Hidx) => /list_find_idx_Some[?[Hl [? Hlt]]].
        * rewrite Hvact.
          iApply (wp_read_reg_acc with "Hr"); [| done|].
          { rewrite /read_accessor/=. by simplify_option_eq. }
          iIntros "% Hr". iApply "Hwp". iApply "Hregs". iExists _. by iFrame.
        * destruct vact as [| | | | | | | rs|] => //.
          move: (Hvact) => /= [Hlen /Forall_fold_right/(Forall_lookup_1 _ _ _ _) Hall].
          have [|[??]?]:= lookup_lt_is_Some_2 rs i.
          { rewrite -Hlen. apply: lookup_lt_is_Some_1. naive_solver. }
          efeed pose proof Hall as Hall'. { rewrite ->lookup_zip_with, Hl. simpl. by simplify_option_eq. }
          destruct Hall'; simplify_eq.
          iApply (wp_read_reg_acc with "Hr"); [| done|]. {
            rewrite /read_accessor/=. apply/bind_Some.
            eexists i. simplify_option_eq. split; [|done].
            apply/list_find_idx_Some. eexists _. split_and! => // j [??]/=??.
            have [|[??] Hjs]:= lookup_lt_is_Some_2 ss j.
            { rewrite Hlen. apply: lookup_lt_is_Some_1. naive_solver. }
            efeed pose proof Hall as Hall'. { rewrite ->lookup_zip_with, Hjs. simpl. by simplify_option_eq. }
            destruct Hall'; simplify_eq. by apply: (Hlt _ (_, _)).
          }
          iIntros "% Hr". iApply "Hwp". iApply "Hregs". iExists _. by iFrame.
  Qed.

  Lemma li_wp_assume_reg r v ann es :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜v = v'⌝ ∗ (r ↦ᵣ v' -∗ WPasm es))
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
                      ⌜∀ v', valu_has_shape v' (regs !!! i).2 → v' = v⌝ ∗ (reg_col regs -∗ WPasm es))
      end)) -∗
    WPasm (AssumeReg r [] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - iDestruct "Hwp" as (->) "?". by iApply (wp_assume_reg with "Hr").
    - iDestruct "Hwp" as (a [[??][?[??]]]%list_find_idx_Some Hr) "Hwp"; simplify_eq/=.
      erewrite list_lookup_total_correct in Hr; [|done]; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
      have ?: vact = v by naive_solver. subst.
      iApply (wp_assume_reg with "Hr"). iIntros "Hr". iApply "Hwp". iApply "Hregs".
      iExists _. by iFrame.
  Qed.

  Lemma li_wp_assume_reg_struct r f v ann es :
    ((find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => ⌜v = v'⌝ ∗ (r # f ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f ∨ x.1 = KindReg r)%type) regs) (λ i,
          ∃ e, ⌜e = (regs !!! i)⌝ ∗
          match e.1 with
          | KindField _ _ => ⌜e.2 = ExactShape v⌝ ∗ (reg_col regs -∗ WPasm es)
          | KindReg _ =>
              if e.2 is ExactShape (RegVal_Struct rs) then
                tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = f)) rs) (λ i,
                  ⌜(rs !!! i).2 = v⌝ ∗ (reg_col regs -∗ WPasm es)) else False
          end)
      end))) -∗
    WPasm (AssumeReg r [Field f] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (?) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - iDestruct "Hwp" as (->) "?". by iApply (wp_assume_reg_struct with "Hr").
    - iDestruct "Hwp" as (i [[??][?[Hor ?]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      erewrite list_lookup_total_correct; [|done].
      iDestruct "Hwp" as (e ->) "Hwp"; simplify_eq/=. destruct Hor; simplify_eq.
      + iDestruct "Hwp" as (->) "Hwp".
        iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
        iApply (wp_assume_reg_struct with "Hr"). iIntros "Hr". iApply "Hwp". iApply "Hregs".
        iExists _. by iFrame.
      + do 2 case_match => //.
        iDestruct "Hwp" as (? Hi ?) "Hwp"; simplify_eq/=.
        move: (Hi) => /list_find_idx_Some [[??][?[? ?]]]; simplify_eq/=.
        erewrite list_lookup_total_correct; [|done]; simplify_eq/=.
        iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
        iApply (wp_assume_reg_acc with "Hr").
        { rewrite /read_accessor /=. by simplify_option_eq. }
        iIntros "Hr". iApply "Hwp". iApply "Hregs".
        iExists _. by iFrame.
  Qed.

  Lemma li_wp_write_reg r v ann es:
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (r ↦ᵣ v -∗ WPasm es)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
          (∀ vr, ⌜regs !! i = Some vr⌝ -∗ reg_col (delete i regs) -∗ r ↦ᵣ v -∗ WPasm es))
      end)) -∗
    WPasm (WriteReg r [] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_write_reg with "Hr").
    - iDestruct "Hwp" as (i [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
      iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
      iApply (wp_write_reg with "Hr"). iIntros "Hr". iApply ("Hwp" with "[] Hregs [$]"). done.
  Qed.

  Lemma li_wp_write_reg_struct r f v ann es:
    (∃ vnew, ⌜read_accessor [Field f] v = Some vnew⌝ ∗
    (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => (r # f ↦ᵣ vnew -∗ WPasm es)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f)) regs) (λ i,
          (∀ vr, ⌜regs !! i = Some vr⌝ -∗ reg_col (delete i regs) -∗ r # f ↦ᵣ vnew -∗ WPasm es))
      end))) -∗
    WPasm (WriteReg r [Field f] v ann :: es).
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (vnew ? rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_write_reg_struct with "Hr").
    - iDestruct "Hwp" as (i [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
      iDestruct "Hr" as "[[%vact [% Hr]] Hregs]".
      iApply (wp_write_reg_struct with "Hr"); [done|]. iIntros "Hr".
      iApply ("Hwp" with "[] Hregs [$]"). done.
  Qed.

  Lemma li_wp_branch_address v ann es:
    WPasm es -∗
    WPasm (BranchAddress v ann :: es).
  Proof. apply: wp_branch_address. Qed.

  Lemma li_wp_branch c desc ann es:
    WPasm es -∗
    WPasm (Branch c desc ann :: es).
  Proof. apply: wp_branch. Qed.

  Lemma li_wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm (subst_trace (Val_Bits n) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof. apply: wp_declare_const_bv. Qed.

  Lemma li_wp_declare_const_bool v es ann:
    (∀ b : bool, WPasm (subst_trace (Val_Bool b) v es)) -∗
    WPasm (Smt (DeclareConst v Ty_Bool) ann :: es).
  Proof. apply: wp_declare_const_bool. Qed.

  Lemma li_wp_declare_const_enum v es i ann:
    (∀ c, WPasm (subst_trace (Val_Enum (i, c)) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :: es).
  Proof. apply: wp_declare_const_enum. Qed.

  Lemma li_wp_define_const n es ann e:
    tactic_hint (compute_wp_exp e) (λ v, let_bind_hint v (λ v, WPasm (subst_trace v n es))) -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof.
    iIntros "Hexp". iApply wp_define_const. unfold let_bind_hint.
    iApply (wpe_wand with "Hexp"). iIntros (?) "$".
  Qed.

  Lemma li_wp_assert es ann e:
    tactic_hint (compute_wp_exp e) (λ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es)) -∗
    WPasm (Smt (Assert e) ann :: es).
  Proof. apply: wp_assert. Qed.

  Lemma li_wp_assume es ann e:
    WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ WPasm es }} -∗
    WPasm (Assume e ann :: es).
  Proof. apply: wp_assume. Qed.

  Lemma li_wp_barrier es v ann:
    WPasm es -∗
    WPasm (Barrier v ann :: es).
  Proof. apply: wp_barrier. Qed.

  Lemma li_wp_write_mem len n success kind a (vnew : bv n) tag ann es:
    (⌜n = (8*len)%N⌝ ∗
    ⌜len ≠ 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (λ mk,
      match mk with
      | MKMapsTo n' vold => ⌜n' = n⌝ ∗ (bv_unsigned a ↦ₘ vnew -∗ WPasm es)
      | MKArray n' a' l =>
          ∃ i : nat, ⌜a' = bv_unsigned a - (i * Z.of_N len)⌝ ∗ ⌜i < length l⌝%nat ∗
          ∃ Heq : n = n', (a' ↦ₘ∗ <[i := (eq_rect n bv vnew n' Heq)]>l -∗ WPasm es)
      | MKUninit a' n' =>
        ⌜a' ≤ bv_unsigned a⌝ ∗ ⌜bv_unsigned a + Z.of_N len ≤ a' + n'⌝ ∗ (
        bv_unsigned a ↦ₘ vnew -∗
        a' ↦ₘ? (bv_unsigned a - a') -∗
        (bv_unsigned a + (Z.of_N len)) ↦ₘ? (a' + n' - (bv_unsigned a + Z.of_N len)) -∗
        WPasm es)
      | MKMMIO a' l =>
        ⌜a' ≤ bv_unsigned a⌝ ∗ ⌜bv_unsigned a + Z.of_N len ≤ a' + l⌝ ∗
        ∃ Pκs Pκs', spec_trace Pκs ∗ ⌜scons (SWriteMem a vnew) Pκs' ⊆ Pκs⌝ ∗
        (spec_trace Pκs' -∗ WPasm es)
      end
    )) -∗
    WPasm (WriteMem (RVal_Bool success) kind (RVal_Bits (BVN 64 a)) (RVal_Bits (BVN n vnew)) len tag ann :: es).
  Proof.
    iDestruct 1 as (?? mk) "[HP Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (->) "Hcont". iApply (wp_write_mem with "HP Hcont"); [done | lia].
    - iDestruct "Hcont" as (i?? Heq) "Hcont". subst => /=.
      iApply (wp_write_mem_array with "HP [Hcont]"); [done|lia|done|done|].
      iIntros "Hl". by iApply "Hcont".
    - iDestruct "Hcont" as (??) "Hcont". subst n.
      iDestruct (mem_mapsto_uninit_split (bv_unsigned a - a0) with "HP") as "[Ha1 Ha2]"; [lia|].
      iDestruct (mem_mapsto_uninit_split (Z.of_N len) with "Ha2") as "[Ha2 Ha3]"; [lia|].
      iDestruct (mem_mapsto_uninit_to_mapsto with "Ha2") as (?? Heq) "Hl".
      rewrite N2Z.id N.mul_comm in Heq. subst.
      have -> : a0 + (bv_unsigned a - a0) = bv_unsigned a by bv_solve.
      iApply (wp_write_mem with "Hl"); [done|lia|]. iIntros "Hl".
      iApply ("Hcont" with "Hl Ha1").
      have -> : (n0 - (bv_unsigned a - a0) - Z.of_N len) = (a0 + n0 - (bv_unsigned a + Z.of_N len)) by lia.
      done.
    - iDestruct "Hcont" as (?? Pκs Pκs') "[Hκs [% Hcont]]"; simplify_eq/=.
      iApply (wp_write_mmio with "[HP] Hκs"); [done | lia| spec_solver | | ].
      { iApply (mmio_range_shorten with "HP"); lia. }
      iIntros "Hspec". iApply "Hcont". iApply (spec_trace_mono with "Hspec").
      spec_solver.
  Qed.

  Lemma li_wp_read_mem len n kind a vread tag ann es:
    (⌜n = (8 * len)%N⌝ ∗
    ⌜len ≠ 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (λ mk,
      match mk with
      | MKMapsTo n' vmem => ∃ Heq : n = n', (⌜(eq_rect n bv vread n' Heq) = vmem⌝ -∗ bv_unsigned a ↦ₘ vmem -∗ WPasm es)
      | MKArray n' a' l => ∃ i : nat, ⌜a' = bv_unsigned a - (i * Z.of_N len)⌝ ∗ ⌜i < length l⌝%nat ∗
         ∃ Heq : n = n', (∀ vmem, ⌜l !! i = Some vmem⌝ -∗ ⌜(eq_rect n bv vread n' Heq) = vmem⌝ -∗ a' ↦ₘ∗ l -∗ WPasm es)
      | MKUninit a' n' => False
      | MKMMIO a' l =>
        ⌜a' ≤ bv_unsigned a⌝ ∗ ⌜bv_unsigned a + Z.of_N len ≤ a' + l⌝ ∗
        ∃ Pκs Pκs', spec_trace Pκs ∗ ⌜scons (SReadMem a vread) Pκs' ⊆ Pκs⌝ ∗
        (spec_trace Pκs' -∗ WPasm es)
      end)) -∗
    WPasm (ReadMem (RVal_Bits (BVN n vread)) kind (RVal_Bits (BVN 64 a)) len tag ann :: es).
  Proof.
    iDestruct 1 as (?? mk) "[Hmem Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (?) "Hcont". subst => /=. iApply (wp_read_mem with "Hmem Hcont"); [done|lia].
    - iDestruct "Hcont" as (i?[??]%lookup_lt_is_Some_2 ?) "Hcont". subst => /=.
      iApply (wp_read_mem_array with "Hmem [Hcont]"); [done|lia|done|done|].
      iIntros (?) "Hl". by iApply "Hcont".
    - done.
    - iDestruct "Hcont" as (?? Pκs Pκs') "[Hκs [% Hcont]]"; simplify_eq/=.
      iApply (wp_read_mmio with "[Hmem] Hκs"); [done | lia| spec_solver | | ].
      { iApply (mmio_range_shorten with "Hmem"); lia. }
      iIntros "Hspec". iApply "Hcont". iApply (spec_trace_mono with "Hspec").
      spec_solver.
  Qed.

  Lemma li_wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. apply: wpe_val. Qed.

  Lemma li_wpae_var_reg r Φ ann :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v => (if v is RegVal_Base v' then r ↦ᵣ v -∗ Φ v' else False)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindReg r)) regs) (λ i,
        ∀ v, ⌜valu_has_shape v (regs !!! i).2⌝ -∗ ∃ v', ⌜v = RegVal_Base v'⌝ ∗ (reg_col regs -∗ Φ v')
             )
      end)) -∗
    WPaexp (AExp_Val (AVal_Var r []) ann) {{ Φ }}.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - case_match => //; subst. by iApply (wpae_var_reg with "Hr").
    - iDestruct "Hwp" as (i [[??][?[??]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      erewrite list_lookup_total_correct; [|done]; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
      iDestruct ("Hwp" with "[//]") as (? ->) "Hwp".
      iApply (wpae_var_reg with "Hr"). iIntros "Hr". iApply "Hwp". iApply "Hregs".
      iExists _. by iFrame.
  Qed.
  Lemma li_wpae_var_struct r f Φ ann :
    (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v => (if v is RegVal_Base v' then r # f ↦ᵣ v -∗ Φ v' else False)
      | RKCol regs => tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = KindField r f ∨ x.1 = KindReg r)%type) regs) (λ i,
          ∃ e, ⌜e = (regs !!! i)⌝ ∗
          match e.1 with
          | KindField _ _ =>
              ∀ v, ⌜valu_has_shape v e.2⌝ -∗ ∃ v', ⌜v = RegVal_Base v'⌝ ∗ (reg_col regs -∗ Φ v')
          | KindReg _ =>
              ∀ v, ⌜valu_has_shape v e.2⌝ -∗ ∃ rs, ⌜v = RegVal_Struct rs⌝ ∗
                tactic_hint (vm_compute_hint (list_find_idx (λ x, x.1 = f)) rs) (λ i,
                  if (rs !!! i).2 is RegVal_Base v' then reg_col regs -∗ Φ v' else False
                 )
          end)
      end)) -∗
    WPaexp (AExp_Val (AVal_Var r [Field f]) ann) {{ Φ }}.
  Proof.
    unfold tactic_hint, vm_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - case_match => //; subst. by iApply (wpae_var_struct with "Hr").
    - iDestruct "Hwp" as (? [[??][?[Hor ?]]]%list_find_idx_Some) "Hwp"; simplify_eq/=.
      erewrite list_lookup_total_correct; [|done].
      iDestruct "Hwp" as (e ->) "Hwp"; simplify_eq/=. destruct Hor; simplify_eq.
      + iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
        iDestruct ("Hwp" with "[//]") as (? ->) "Hwp".
        iApply (wpae_var_struct with "Hr"). iIntros "Hr". iApply "Hwp". iApply "Hregs".
        iExists _. by iFrame.
      + iDestruct (big_sepL_lookup_acc with "Hr") as "[[%vact [% Hr]] Hregs]"; [done|]; simplify_eq/=.
        iDestruct ("Hwp" with "[//]") as (? ->) "Hwp". iDestruct "Hwp" as (? Hi) "Hwp".
        move: (Hi) => /list_find_idx_Some [[??][?[? ?]]]; simplify_eq/=.
        erewrite list_lookup_total_correct; [|done]; simplify_eq/=. case_match => //.
        iApply (wpae_var_reg_acc with "Hr").
        { rewrite /read_accessor /=. by simplify_option_eq. }
        iIntros "Hr". iApply "Hwp". iApply "Hregs". iExists _. by iFrame.
  Qed.

  Lemma li_wpae_bits b Φ ann:
    Φ (Val_Bits b) -∗
    WPaexp (AExp_Val (AVal_Bits b) ann) {{ Φ }}.
  Proof. apply: wpae_bits. Qed.
  Lemma li_wpae_bool b Φ ann:
    Φ (Val_Bool b) -∗
    WPaexp (AExp_Val (AVal_Bool b) ann) {{ Φ }}.
  Proof. apply: wpae_bool. Qed.
  Lemma li_wpae_enum b Φ ann:
    Φ (Val_Enum b) -∗
    WPaexp (AExp_Val (AVal_Enum b) ann) {{ Φ }}.
  Proof. apply: wpae_enum. Qed.

  Lemma li_wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPexp (Manyop op es ann) {{ Φ }}.
  Proof. apply: wpe_manyop. Qed.
  Lemma li_wpae_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPaexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPaexp (AExp_Manyop op es ann) {{ Φ }}.
  Proof. apply: wpae_manyop. Qed.

  Lemma li_wpe_unop op e Φ ann:
    WPexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPexp (Unop op e ann) {{ Φ }}.
  Proof. apply: wpe_unop. Qed.
  Lemma li_wpae_unop op e Φ ann:
    WPaexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPaexp (AExp_Unop op e ann) {{ Φ }}.
  Proof. apply: wpae_unop. Qed.

  Lemma li_wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof. apply: wpe_binop. Qed.
  Lemma li_wpae_binop op e1 e2 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPaexp (AExp_Binop op e1 e2 ann) {{ Φ }}.
  Proof. apply: wpae_binop. Qed.

  Lemma li_wpe_ite e1 e2 e3 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, WPexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPexp (Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. apply: wpe_ite. Qed.
  Lemma li_wpae_ite e1 e2 e3 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, WPaexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPaexp (AExp_Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. apply wpae_ite. Qed.
End instances.

#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ _) (_ ↦ₘ _) _) =>
  ( apply tac_mem_mapsto_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ∗ _) (_ ↦ₘ∗ _) _) =>
  ( apply tac_mem_mapsto_array_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ? _) (_ ↦ₘ? _) _) =>
  ( apply tac_mem_mapsto_uninit_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (mmio_range _ _) (mmio_range _ _) _) =>
  ( apply tac_mem_mapsto_mmio; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICRegMapstoSemantic _) (reg_col _) (reg_col _) _) =>
( apply tac_reg_mapsto_reg_col; vm_compute; eexists _; done) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICStructRegMapstoSemantic _ _) (reg_col _) (reg_col _) _) =>
( apply tac_struct_reg_mapsto_reg_col; vm_compute; eexists _; done) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr_pre' _ _ _) (instr_pre' _ _ _) _) =>
  ( apply tac_instr_pre_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr _ _) (instr _ _) _) =>
  ( apply tac_instr_eq; bv_solve) : typeclass_instances.

(* TODO: upstream? *)
Global Opaque FindHypEqual.

(* TODO: upstream? *)
Lemma tac_entails_to_simplify_hyp {Σ} (P Q : iProp Σ):
  (P ⊢ Q)%I → ∀ G, (Q -∗ G) -∗ simplify_hyp P G.
Proof. move => ??. by apply bi.wand_mono. Qed.
Definition entails_to_simplify_hyp {Σ} (n : N) {P Q : iProp Σ} (Hent : (P ⊢ Q)%I) :
  SimplifyHyp P (Some n) :=
  λ G, i2p (tac_entails_to_simplify_hyp P Q Hent G).

(* TODO: upstream? *)
Ltac liLetBindHint :=
  idtac;
  match goal with
  | |- envs_entails ?Δ (let_bind_hint ?x ?f) =>
    let H := fresh "LET" in
    lazymatch x with
    | Val_Bits (bv_to_bvn ?y) =>
      lazymatch y with
      | _ _ =>
        pose (H := y);
        change (envs_entails Δ (f (Val_Bits (bv_to_bvn H)))); cbn beta
      | _ => (* No application, probably just another let binding. Don't create a new one.  *)
        change (envs_entails Δ (f x)); cbn beta
      end
    | Val_Bool ?y =>
      lazymatch y with
      | _ _ =>
        pose (H := y);
        change (envs_entails Δ (f (Val_Bool H))); cbn beta
      | _ => (* No application, probably just another let binding. Don't create a new one.  *)
        change (envs_entails Δ (f x)); cbn beta
      end
    end
  end.

Definition TRACE_LET {A} (x : A) : A := x.
Arguments TRACE_LET : simpl never.
Notation "'HIDDEN'" := (TRACE_LET _) (only printing).


Ltac liAIntroduceLetInGoal :=
  (* kill old unused TRACE_LET. This can happen e.g. because of subst_event unfolding TRACE_LET. *)
  try match goal with | H := TRACE_LET _ |- _ => clear H end;
  lazymatch goal with
  | |- envs_entails ?Δ ?P =>
    lazymatch P with
    | wp_exp ?e ?Φ =>
      let H := fresh "GOAL" in
      pose H := (LET_ID Φ);
      change_no_check (envs_entails Δ (wp_exp e H))
    | wp_a_exp ?e ?Φ =>
      let H := fresh "GOAL" in
      pose H := (LET_ID Φ);
      change_no_check (envs_entails Δ (wp_a_exp e H))
    | WPasm (?e::?es) =>
      let H := fresh "TRACE" in
      assert_fails (is_var es);
      pose H := (TRACE_LET es);
      change_no_check (envs_entails Δ (WPasm (e::H)))
    | WPasm (TRACE_LET (?e::?es)) =>
      let H := fresh "TRACE" in
      pose H := (TRACE_LET es);
      change_no_check (envs_entails Δ (WPasm (e::H)))
    | WPasm (TRACE_LET []) =>
      change_no_check (envs_entails Δ (WPasm []))
    | (?r ↦ᵣ: ?P)%I =>
      let H := fresh "GOAL" in
      pose H := (LET_ID P);
      change_no_check (envs_entails Δ (r ↦ᵣ: H))
    | (?r # ?f ↦ᵣ: ?P)%I =>
      let H := fresh "GOAL" in
      pose H := (LET_ID P);
      change_no_check (envs_entails Δ (r # f ↦ᵣ: H))
    end
  end
.

Global Arguments subst_trace : simpl never.

Ltac liAAsm :=
  lazymatch goal with
  | |- envs_entails ?Δ (WPasm ?es) =>
    lazymatch es with
    | [] => notypeclasses refine (tac_fast_apply (li_wp_next_instr) _)
    | ?e :: _ =>
      lazymatch e with
      | ReadReg _ [] _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_reg _ _ _ _) _)
      | ReadReg _ [Field _] _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_reg_struct _ _ _ _ _) _)
      | AssumeReg _ [] _ _ => notypeclasses refine (tac_fast_apply (li_wp_assume_reg _ _ _ _) _)
      | AssumeReg _ [Field _] _ _ => notypeclasses refine (tac_fast_apply (li_wp_assume_reg_struct _ _ _ _ _) _)
      | WriteReg _ [] _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_reg _ _ _ _) _)
      | WriteReg _ [Field _] _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_reg_struct _ _ _ _ _) _)
      | BranchAddress _ _ => notypeclasses refine (tac_fast_apply (li_wp_branch_address _ _ _) _)
      | Branch _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_branch _ _ _ _) _)
      | ReadMem _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_mem _ _ _ _ _ _ _ _) _)
      | WriteMem _ _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_mem _ _ _ _ _ _ _ _ _) _)
      | Smt (DeclareConst _ (Ty_BitVec _)) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bv _ _ _ _) _)
      | Smt (DeclareConst _ Ty_Bool) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bool _ _ _) _)
      | Smt (DeclareConst _ (Ty_Enum _)) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_enum _ _ _ _) _)
      | Smt (DefineConst _ _) _ => notypeclasses refine (tac_fast_apply (li_wp_define_const _ _ _ _) _)
      | Smt (Assert _) _ => notypeclasses refine (tac_fast_apply (li_wp_assert _ _ _) _)
      | Assume _ _ => notypeclasses refine (tac_fast_apply (li_wp_assume _ _ _) _)
      | Barrier _ _ => notypeclasses refine (tac_fast_apply (li_wp_barrier _ _ _) _)
      end
    | subst_trace _ _ ?t => iEval (
       try unfold t;
       lazy [TRACE_LET subst_trace fmap subst_val_event subst_val_smt subst_val_exp
             subst_val_base_val eq_var_name Z.eqb Pos.eqb subst_val_valu map list_fmap ])
    | ?def => first [
                 iEval (unfold def); try clear def
               | fail "liAAsm: unknown asm" es
               ]
    end
  | |- envs_entails ?Δ (instr_pre' _ _ _) =>
    notypeclasses refine (tac_fast_apply (li_instr_pre _ _ _) _)
  end.

Ltac liAExp :=
  lazymatch goal with
  (* | |- envs_entails ?Δ (wp_exp ?e _) => *)
    (* lazymatch e with *)
    (* | Val _ _ => notypeclasses refine (tac_fast_apply (li_wpe_val _ _ _) _) *)
    (* | Manyop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_manyop _ _ _ _) _) *)
    (* | Unop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_unop _ _ _ _) _) *)
    (* | Binop _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_binop _ _ _ _ _) _) *)
    (* | Ite _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_ite _ _ _ _ _) _) *)
    (* | _ => fail "liAExp: unknown exp" e *)
    (* end *)
  | |- envs_entails ?Δ (wp_a_exp ?e _) =>
    lazymatch e with
    | AExp_Val (AVal_Var _ []) _ => notypeclasses refine (tac_fast_apply (li_wpae_var_reg _ _ _) _)
    | AExp_Val (AVal_Var _ [Field _]) _ => notypeclasses refine (tac_fast_apply (li_wpae_var_struct _ _ _ _) _)
    | AExp_Val (AVal_Bits _) _ => notypeclasses refine (tac_fast_apply (li_wpae_bits _ _ _) _)
    | AExp_Val (AVal_Bool _) _ => notypeclasses refine (tac_fast_apply (li_wpae_bool _ _ _) _)
    | AExp_Val (AVal_Enum _) _ => notypeclasses refine (tac_fast_apply (li_wpae_enum _ _ _) _)
    | AExp_Manyop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpae_manyop _ _ _ _) _)
    | AExp_Unop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpae_unop _ _ _ _) _)
    | AExp_Binop _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpae_binop _ _ _ _ _) _)
    | AExp_Ite _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpae_ite _ _ _ _ _) _)
    | _ => fail "liAExp: unknown a_exp" e
    end
  end.

Class LithiumUnfold {A} (x : A) : Prop := lithium_unfold_proof : True.

Ltac li_do_unfold P :=
  let h := get_head P in
  let x := constr:(_ : LithiumUnfold h) in
  iEval (progress unfold h).

Ltac liUnfoldEarly :=
  lazymatch goal with
  | |- envs_entails ?Δ (?P -∗ ?Q) => li_do_unfold P
  | |- envs_entails ?Δ (?P ∗ ?Q) => li_do_unfold P
  end.

Ltac liUnfoldLate :=
  lazymatch goal with
  | |- envs_entails ?Δ (?P) => li_do_unfold P
  end.

Ltac liAOther :=
  lazymatch goal with
  | |- envs_entails ?Δ ?P =>
    lazymatch P with
    | (_ ↦ᵣ: _)%I => notypeclasses refine (tac_fast_apply (reg_mapsto_pred_intro _ _) _)
    end
  end.

Ltac liAStep :=
 liEnforceInvariantAndUnfoldInstantiatedEvars;
 try liAIntroduceLetInGoal;
 first [
    liAAsm
  | liAExp
  | liAOther
  | liUnfoldEarly
  | liStep
  | liLetBindHint
  | liUnfoldLate
]; liSimpl.
