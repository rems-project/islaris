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

From iris.proofmode Require Import coq_tactics reduction.
From lithium Require Import hooks.
From lithium Require Export all.
From stdpp.unstable Require Export bitvector_tactics.
From isla Require Export lifting.
Set Default Proof Using "Type".

Lemma bv_unfold_ite s w n b1 b2 z1 z2 b:
  BvUnfold n s w b1 z1 →
  BvUnfold n s w b2 z2 →
  BvUnfold n s w (ite b b1 b2) (ite b z1 z2).
Proof. move => [Hz1] [Hz2]. constructor. destruct w, s, b; naive_solver. Qed.
Global Hint Resolve bv_unfold_ite | 10 : bv_unfold_db.

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
  SimplBoth (ite b (BV 1 1) (BV 1 0) = (BV 1 1)) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_1_0_neq_1_simpl b :
  SimplBoth (ite b (BV 1 1) (BV 1 0) ≠ (BV 1 1)) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_1_0_eq_0_simpl b :
  SimplBoth (ite b (BV 1 1) (BV 1 0) = (BV 1 0)) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_1_0_neq_0_simpl b :
  SimplBoth (ite b (BV 1 1) (BV 1 0) ≠ (BV 1 0)) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_eq_1_simpl b :
  SimplBoth (ite b (BV 1 0) (BV 1 1) = (BV 1 1)) (b = false).
Proof. by destruct b. Qed.
Global Instance ite_0_1_neq_1_simpl b :
  SimplBoth (ite b (BV 1 0) (BV 1 1) ≠ (BV 1 1)) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_eq_0_simpl b :
  SimplBoth (ite b (BV 1 0) (BV 1 1) = (BV 1 0)) (b = true).
Proof. by destruct b. Qed.
Global Instance ite_0_1_neq_0_simpl b :
  SimplBoth (ite b (BV 1 0) (BV 1 1) ≠ (BV 1 0)) (b = false).
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

Global Instance simpl_impl_valu_has_shape_mask v n m z:
  SimplImpl (valu_has_shape v (MaskShape n m z))
        (∃ b : bv n, v = RVal_Bits b ∧ Z.land (bv_unsigned b) m = z).
Proof. split; [naive_solver|]. move => /valu_has_mask_shape. naive_solver. Qed.
Global Instance simpl_impl_valu_has_shape_bits v n:
  SimplImpl (valu_has_shape v (BitsShape n)) (∃ b : bv n, v = RVal_Bits b).
Proof. split; [naive_solver|]. move => /valu_has_bits_shape. naive_solver. Qed.
(* unsafe because proving both directions is annoying *)
Global Instance simpl_impl_valu_struct_shape v ss :
  SimplImplUnsafe true (valu_has_shape v (StructShape ss)) (foldr (λ s (T : _ → Prop) rs, ∃ v, valu_has_shape v s.2 ∧ T (rs ++ [(s.1, v)])) (λ rs, v = RegVal_Struct rs) ss []).
Proof.
  unfold SimplImplUnsafe. move Hrs': {2}[] => rs'.
  destruct v as [| | | | | | rs | |] => //= -[Hlen /Forall_fold_right Hall].
  have Hrs: rs = rs' ++ rs by simplify_list_eq. clear Hrs'.
  elim: ss {1 3 4}rs rs' Hlen Hrs Hall.
  { move => []//=?? ->. rewrite app_nil_r. naive_solver. }
  move => [??] ss IH [|[??]?]//= ? [?] ? /list.Forall_cons[[??]?]. simplify_eq/=.
  eexists _. split; [done|]. apply: IH; [done| |done]. by simplify_list_eq.
Qed.

Global Instance simpl_and_bv_and_0xfff0000000000000 b :
  SimplAnd (bv_and b (BV 64 0xfff0000000000000) = (BV 64 0)) (bv_unsigned b < 2 ^ 52).
Proof.
  split; move => Hb.
  - bv_simplify. bitblast. eapply Z.bounded_iff_bits_nonneg; [| |done|]; bv_solve.
  - eapply Z.bounded_iff_bits_nonneg; [lia | bv_solve|] => l ?. bitblast.
    bv_simplify Hb. by bitblast Hb with l.
Qed.

Global Instance simpl_and_bv_and_0xfff0000000000007 b :
  SimplAnd (bv_and b (BV 64 0xfff0000000000007) = (BV 64 0)) (bv_unsigned b < 2 ^ 52 ∧ bv_unsigned b `mod` 8 = 0).
Proof.
  split.
  - move => [Hb Hmod].
    bv_simplify. bitblast as i.
    + by bitblast Hmod with i.
    + eapply Z.bounded_iff_bits_nonneg; [| |done|]; bv_solve.
  - move => Hb. bv_simplify Hb. split.
    + eapply Z.bounded_iff_bits_nonneg; [lia|bv_solve|] => l ?. bitblast.
      by bitblast Hb with l.
    + bitblast as i. by bitblast Hb with i.
Qed.

(** * [normalize_instr_addr] *)
Definition normalize_instr_addr {Σ} (a1 : Z) (T : Z → iProp Σ) : iProp Σ :=
  ∃ a2, ⌜bv_wrap 64 a1 = bv_wrap 64 a2⌝ ∗ T a2.
Arguments normalize_instr_addr : simpl never.
Global Typeclasses Opaque normalize_instr_addr.

Program Definition normalize_instr_addr_hint {Σ} a1 a2 :
  (bv_wrap 64 a1 = bv_wrap 64 a2) →
  LiTactic (normalize_instr_addr (Σ:=Σ) a1) := λ H, {|
    li_tactic_P T := T a2;
|}.
Next Obligation. unfold normalize_instr_addr. move => ??? -> ?. iIntros "?". iExists _. by iFrame. Qed.

Lemma normalize_instr_addr_add_tac a n r:
  bv_wrap 64 (a + bv_unsigned n) = r →
  bv_wrap 64 (bv_unsigned (bv_add (Z_to_bv 64 a) n)) = r.
Proof. move => <-. by rewrite bv_add_unsigned Z_to_bv_unsigned bv_wrap_bv_wrap // bv_wrap_add_idemp_l. Qed.

(* This kind of addresses appear for ret on riscv64 *)
Lemma normalize_instr_addr_riscv64_ret_tac a r:
  bv_extract 0 1 a = (BV 1 0) →
  bv_wrap 64 (bv_unsigned a) = r →
  bv_wrap 64 (bv_unsigned (bv_or (bv_and (bv_add a (BV 64 0)) (BV 64 0xfffffffffffffffe))  (BV 64 0))) = r.
Proof.
  move => Ha <-. have -> : (bv_add a (BV 64 0)) = a by bv_solve.
  f_equal. bv_simplify. bv_simplify Ha. bitblast as i. by bitblast Ha with i.
Qed.

Ltac solve_normalize_instr_addr :=
  unfold normalize_instr_addr; unLET;
  try lazymatch goal with
  | |- bv_wrap _ ?a = _ => reduce_closed a
  end;
  try lazymatch goal with
  | |- bv_wrap _ (bv_unsigned (bv_add (Z_to_bv 64 _) _)) = _ => apply normalize_instr_addr_add_tac
  end;
  try lazymatch goal with
  | |- bv_wrap _ (bv_unsigned (bv_or (bv_and (bv_add _ _) _) _)) = _ => apply normalize_instr_addr_riscv64_ret_tac;[done|]
  end;
  try lazymatch goal with
  | |- bv_wrap _ (_ + ?a) = _ => reduce_closed a
  end;
  exact: eq_refl.

Global Hint Extern 10 (LiTactic (normalize_instr_addr _)) =>
  eapply normalize_instr_addr_hint; solve_normalize_instr_addr : typeclass_instances.


(** * [normalize_bv_wrap] *)
Definition normalize_bv_wrap {Σ} (a1 : Z) (T : Z → iProp Σ) : iProp Σ :=
  ∃ a2, ⌜bv_wrap 64 a1 = bv_wrap 64 a2⌝ ∗ T a2.
Arguments normalize_bv_wrap : simpl never.
Global Typeclasses Opaque normalize_bv_wrap.

Program Definition normalize_bv_wrap_hint {Σ} a1 a2 :
  (∀ x, bv_wrap 64 a2 = x → block bv_wrap 64%N a1 = x) →
  LiTactic (normalize_bv_wrap (Σ:=Σ) a1) := λ H, {|
    li_tactic_P T := T a2;
|}.
Next Obligation. unfold normalize_bv_wrap, block. move => ??? Heq ?. iIntros "?". iExists _. iFrame. iPureIntro. by apply: Heq. Qed.

(* Transform constants bigger than bv_modulus 64 - 256 into negative numbers *)
#[export] Hint Extern 10 (BvWrapSimplify 64 (Z.pos ?p) ?z) =>
  assert_succeeds (
    lazymatch isPcst p with | true => idtac end;
    assert (bv_modulus 64 - 256 ≤ Z.pos p) by done
    );
  let x := eval vm_compute in (Z.pos p - bv_modulus 64) in
  unify z x;
  constructor;
  done
  : bv_wrap_simplify_db.

Ltac solve_normalize_bv_wrap :=
  let H := fresh in move => ? H;
  bv_simplify;
  repeat match goal with | |- context [bv_wrap ?n ?x] => reduce_closed (bv_wrap n x) end;
  unfold block;
  bv_wrap_simplify_left;
  lazymatch goal with | |- bv_wrap _ ?z = _ => ring_simplify z end;
  apply H.

Global Hint Extern 10 (LiTactic (normalize_bv_wrap _)) =>
  eapply normalize_bv_wrap_hint; solve_normalize_bv_wrap : typeclass_instances.

(** * [compute_wp_exp] *)
Definition compute_wp_exp {Σ} `{!islaG Σ} (e : exp) (T : base_val → iProp Σ) : iProp Σ :=
  WPexp e {{ T }}.
Arguments compute_wp_exp : simpl never.
Global Typeclasses Opaque compute_wp_exp.

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
  LiTactic (compute_wp_exp e) := λ H, {|
    li_tactic_P T := T v;
|}.
Next Obligation.
  iIntros (??????) "HT". rewrite /compute_wp_exp wp_exp_unfold. iExists _. iFrame. iPureIntro.
  apply eval_exp'_sound. naive_solver.
Qed.

(* TODO: one could use vm_compute instead of lazy here by
parametrizing eval_exp' by the operations that vm_compute should not
reduce (e.g., bv_add) and then generalizing them (and all part of the
goal that should not be reduced) before calling vm_compute. Also
vm_compute does not reduce in parameters of inductions, but unclear if
this is useful (if one defines a function [Definition test_to_A {A} (x : A) (X : test x) : A := x],
then vm_compute still reduces x). *)
Ltac solve_compute_wp_exp :=
  let H := fresh in move => ? H;
  lazy [eval_exp' mapM mbind option_bind eval_unop eval_manyop eval_binop option_fmap option_map fmap mret option_ret foldl bvn_to_bv decide decide_rel BinNat.N.eq_dec N.eq_dec N_rec N_rect bvn_n sumbool_rec sumbool_rect BinPos.Pos.eq_dec Pos.eq_dec positive_rect positive_rec eq_rect eq_ind_r eq_ind eq_sym bvn_val N.add N.sub Pos.add Pos.succ mguard option_guard Pos.sub_mask Pos.double_mask Pos.succ_double_mask Pos.pred_double Pos.double_pred_mask];
  lazymatch goal with | |- Some _ = _ => idtac | |- ?G => idtac "solve_compute_wp_exp failed:" G; fail end;
  autorewrite with isla_coq_rewrite;
  apply H.

Global Hint Extern 10 (LiTactic (compute_wp_exp _)) =>
  eapply compute_wp_exp_hint; solve_compute_wp_exp : typeclass_instances.

(** ** [regcol_compute_hint] *)
Definition regcol_compute_hint {Σ A B} (f : A → option B) (x : A) (T : B → iProp Σ) : iProp Σ :=
  ∃ y, ⌜f x = Some y⌝ ∗ T y.
Arguments regcol_compute_hint : simpl never.
Global Typeclasses Opaque regcol_compute_hint.

Program Definition regcol_compute_hint_hint {Σ A B} x (f : A → option B) a :
  f a = Some x →
  LiTactic (regcol_compute_hint (Σ:=Σ) f a) := λ H, {|
    li_tactic_P T := T x;
|}.
Next Obligation. move => ????????. iIntros "HT". iExists _. iFrame. iPureIntro. naive_solver. Qed.

Ltac is_var_no_let v :=
  is_var v;
  assert_fails (clearbody v).
(** [is_fully_reduced_valu v] determines if the valu v is already
fully reduced. If this is the case, one does not need to protect it
from vm_compute. *)
Ltac is_fully_reduced_valu v :=
  first [ is_var_no_let v |
    lazymatch v with
    | RegVal_Base ?b => first [ is_var_no_let b |
      lazymatch b with
      | Val_Bits ?b' => first [ is_var_no_let b' |
        lazymatch b' with
        | @bv_to_bvn ?n ?b'' => first [ is_var_no_let b'' |
          lazymatch b'' with
          | @BV _ ?z _  => first [ is_var_no_let z |
                        lazymatch isZcst z with
                        | true => idtac
                        end
            ]
          end
          ]
        end
      ]
      | Val_Bool ?b' => first [ is_var_no_let b' |
        lazymatch b' with
        | true => idtac
        | false => idtac
        end
      ]
      | Val_Enum ?e => first [ is_var_no_let e |
        lazymatch e with
        | _ => is_var_no_let e
        end
      ]
      end
    ]
    end
  ].

(** Testing [is_fully_reduced_valu] *)
Goal ∀ (v : valu) (b : base_val) (b1 : bool) (b2 : bv 64) (z : Z) Heq,
    let x := bv_add b2 b2 in @BV 64 z Heq = @BV 64 z Heq.
  move => v b b1 b2 z Heq x.
  is_fully_reduced_valu v.
  is_fully_reduced_valu (RegVal_Base b).
  is_fully_reduced_valu (RVal_Bool b1).
  is_fully_reduced_valu (RVal_Bool true).
  is_fully_reduced_valu (RVal_Bool false).
  assert_fails (is_fully_reduced_valu (RVal_Bool (negb true))).
  is_fully_reduced_valu (RVal_Bits b2).
  assert_fails (is_fully_reduced_valu (RVal_Bits (bv_zero_extend 128 b2))).
  is_fully_reduced_valu (RVal_Bits (@BV 64 z Heq)).
  is_fully_reduced_valu (RVal_Bits (BV 64 100)).
  assert_fails (is_fully_reduced_valu (RVal_Bits x)).
  (* is_fully_reduced_valu (RVal_Enum "Machine"). *)
Abort.

Ltac remember_regcol :=
  repeat match goal with
   | |- context [ExactShape ?v] =>
     assert_fails (is_fully_reduced_valu v);
     let H := fresh "H" in move: (v) => H
   | |- context [PropShape ?v] =>
     assert_fails (is_var v);
     let H := fresh "H" in move: (v) => H
   end.

Create HintDb regcol_compute_unfold discriminated.

Ltac solve_regcol_compute_hint :=
  clear;
  autounfold with regcol_compute_unfold;
  repeat match goal with | H := _ |- _  => clearbody H end;
  remember_regcol;
  lazymatch goal with
  | |- LiTactic (regcol_compute_hint ?f ?a) =>
      (* We first compute the result of f a such that we don't need to
      create an evor for it, but can use [abstract]. This is important
      since the [clearbody]s above are otherwise ignored at Qed time,
      leading to divergence of vm_compute. This means that we run
      vm_compute twice, but it should be fast anyway. *)
      let x := eval vm_compute in (f a) in
      lazymatch x with
      | Some ?y => apply (regcol_compute_hint_hint y)
      end
  end;
  abstract (vm_compute; exact eq_refl).

Global Hint Extern 10 (LiTactic (regcol_compute_hint _ _)) =>
  solve_regcol_compute_hint : typeclass_instances.


(** * functions to compute on a regcol *)
Fixpoint regcol_lookup (r : reg_kind) (regs : list (reg_kind * valu_shape)) : option (nat * valu_shape) :=
  match regs with
  | (r', s)::regs' =>
      if reg_kind_eqb r r' then
        Some (0%nat, s)
      else
        prod_map S id <$> regcol_lookup r regs'
  | [] => None
  end.
Lemma regcol_lookup_Some `{!islaG Σ} `{!threadG} r regs s:
  regcol_lookup r regs = Some s →
  regs !! s.1 = Some (r, s.2).
Proof.
  elim: regs s => //= -[??] ? IH [??]. rewrite reg_kind_eqb_eq => Hr. case_bool_decide; simplify_eq/= => //.
  move: Hr => /fmap_Some[[??][??]]. simplify_eq/=.
  by apply (IH (_, _)).
Qed.

Fixpoint regcol_lookup_field (r f : string) (regs : list (reg_kind * valu_shape)) : option (bool * valu_shape) :=
  match regs with
  | (r', s)::regs' =>
      if reg_kind_eqb (KindField r f) r' then
        Some (true, s)
      else if reg_kind_eqb (KindReg r) r' then
        match s with
        | StructShape ss => (λ x, (false, x.2.2)) <$> list_find_bool (λ x, x.1 =? f)%string ss
        | ExactShape (RegVal_Struct rs) =>
            (λ x, (false, ExactShape x.2.2)) <$> list_find_bool (λ x, x.1 =? f)%string rs
        | _ => None
        end
      else regcol_lookup_field r f regs'
  | [] => None
  end.
Lemma regcol_lookup_field_Some `{!islaG Σ} `{!threadG} r f regs s:
  regcol_lookup_field r f regs = Some s →
  reg_col regs -∗ ∃ v v',
      let P := (if s.1 then r # f ↦ᵣ v else r ↦ᵣ v' ∗ ⌜read_accessor [Field f] v' = Some v⌝)%I in
      ⌜valu_has_shape v s.2⌝ ∗ P ∗ (P -∗ reg_col regs).
Proof.
  iIntros (Hr) "Hregs". iInduction regs as [|[r' s'] regs'] "IH" forall (s Hr) => //.
  rewrite ->reg_col_cons. iDestruct "Hregs" as "[[%v [%Hs Hv]] Hregs]".
  simpl in *. destruct r' as [r'|r' f'].
  - rewrite String_eqb_eq in Hr. case_bool_decide; simplify_eq/=.
    + destruct s' as [[]| | | | |] => //; move: Hr => /fmap_Some[[i[??]][Hr ?]]; simplify_eq/=.
      all: rewrite list_find_bool_list_find in Hr; move: Hr => /list_find_Some[?[Hb Hnot]].
      all: rewrite String_eqb_eq bool_decide_spec in Hb; simplify_eq/=.
      all: setoid_rewrite String_eqb_eq in Hnot; setoid_rewrite bool_decide_spec in Hnot.
      * iExists _, _. rewrite ->reg_col_cons. iSplit; [done|]. iFrame. iSplit. {
          iPureIntro. rewrite /read_accessor => /=. apply bind_Some. eexists _. split.
          { apply list_find_idx_Some. by eexists (_, _). }
          apply bind_Some. by eexists _.
        }
        iIntros "[? %]". iExists _. by iFrame.
      * destruct v as [| | | | | |rs| |] => //; simplify_eq/=.
        move: Hs => [Hlen Hall'']. move: (Hall'') => /Forall_fold_right/(Forall_lookup_1 _ _ _ _)Hall.
        have [|[??]?]:= lookup_lt_is_Some_2 rs i.
        { rewrite -Hlen. apply: lookup_lt_is_Some_1. naive_solver. }
        efeed pose proof Hall as Hall'. { by rewrite ->lookup_zip_with; simplify_option_eq. }
        destruct Hall' as [??]; simplify_eq.
        iExists _, _. rewrite ->reg_col_cons. iSplit; [done|]. iFrame. iSplit. {
          iPureIntro. rewrite /read_accessor => /=. apply bind_Some. eexists _. split.
          2: { apply bind_Some. by eexists _. }
          apply list_find_idx_Some. eexists (_, _). split_and! => //. move => j[??]?/=.
          have [|[??]?]:= lookup_lt_is_Some_2 ss j.
          { rewrite Hlen. apply: lookup_lt_is_Some_1. naive_solver. }
          efeed pose proof Hall as Hall'. { by rewrite ->lookup_zip_with; simplify_option_eq. }
          eapply (Hnot _ (_, _)). naive_solver.
        }
        iIntros "[? %]". iExists _. by iFrame.
    + iDestruct ("IH" with "[//] Hregs") as (???) "[? Hregs]". iExists _, _. iSplit;[done|]. iFrame.
      iIntros "Hr". rewrite ->reg_col_cons. iDestruct ("Hregs" with "Hr") as "$". eauto with iFrame.
  - rewrite !String_eqb_eq andb_bool_decide in Hr. case_bool_decide; destruct_and?; simplify_eq/=.
    + iExists _, _. rewrite ->reg_col_cons. iSplit; [done|]. iFrame. iIntros "?". iExists _. by iFrame.
    + iDestruct ("IH" with "[//] Hregs") as (???) "[? Hregs]". iExists _, _. iSplit;[done|]. iFrame.
      iIntros "Hr". rewrite ->reg_col_cons. iDestruct ("Hregs" with "Hr") as "$". eauto with iFrame.
      Unshelve. all: by apply inhabitant.
Qed.

Fixpoint regcol_extract (r : reg_kind) (regs : list (reg_kind * valu_shape)) : option (valu_shape * list (reg_kind * valu_shape)) :=
  match regs with
  | (r', s)::regs' =>
      if reg_kind_eqb r r' then
        Some (s, regs')
      else
        prod_map id ((r',s)::.) <$> regcol_extract r regs'
  | [] => None
  end.
Lemma regcol_extract_Some `{!islaG Σ} `{!threadG} r regs s:
  regcol_extract r regs = Some s →
  reg_col regs -∗ ∃ v, ⌜valu_has_shape v s.1⌝ ∗ r ↦ᵣₖ v ∗ reg_col s.2.
Proof.
  iIntros (Hr) "Hregs". iInduction regs as [|[r' s'] regs'] "IH" forall (s Hr) => //.
  rewrite reg_col_cons. iDestruct "Hregs" as "[[%v [% Hv]] Hregs]".
  simpl in *. rewrite reg_kind_eqb_eq in Hr. case_bool_decide; simplify_eq/=.
  { iExists _. by iFrame. }
  move: Hr => /fmap_Some[[??]/=[??]]; subst => /=.
  iDestruct ("IH" with "[//] Hregs") as (v' ?) "[? ?]" => /=.
  iExists _. rewrite reg_col_cons. iFrame. iSplit; [done|].
  iExists _. by iFrame.
Qed.

Fixpoint regcol_cancel (regs1 regs2 : list (reg_kind * valu_shape)) : list (reg_kind * valu_shape) * list (reg_kind * valu_shape) * list (valu_shape * valu_shape) :=
  match regs2 with
  | (r, s2)::rs =>
      if regcol_extract r regs1 is Some (s1, regs1') then
        let '(regs1'', regs2'', c) := regcol_cancel regs1' rs in
        let i := valu_shape_implies_trivial s1 s2 in
        (regs1'', regs2'', if i then c else (s1, s2)::c)
      else
        let '(regs1'', regs2'', c) := regcol_cancel regs1 rs in
        (regs1'', (r, s2)::regs2'', c)
  | [] => (regs1, [], [])
  end.
Lemma regcol_cancel_sound `{!islaG Σ} `{!threadG} regs1 regs2 res:
  regcol_cancel regs1 regs2 = res →
  Forall (λ c, ∀ v, valu_has_shape v c.1 → valu_has_shape v c.2) res.2 →
  reg_col regs1 -∗ reg_col res.1.1 ∗ (reg_col res.1.2 -∗ reg_col regs2).
Proof.
  iIntros (Hres Hc) "Hregs1".
  iInduction regs2 as [|[r2 s2] regs2] "IH" forall (regs1 res Hres Hc); simplify_eq/=.
  { iFrame. iIntros "$". }
  destruct (regcol_extract r2 regs1) as [[? regs1']|] eqn:He.
  - iDestruct (regcol_extract_Some with "Hregs1") as (v1 ?) "[? Hregs1]"; [done|].
    destruct (regcol_cancel regs1' regs2) as [[??]?] eqn:?; simplify_eq/=.
    iDestruct ("IH" with "[//] [%] Hregs1") as "[$ H2]" => /=.
    { case_match => //. by apply: Forall_inv_tail. }
    iIntros "Hregs". rewrite reg_col_cons. iDestruct ("H2" with "Hregs") as "$".
    iExists _. iFrame. iPureIntro.
    case_match.
    + apply: valu_shape_implies_sound; [|done]. by apply valu_shape_implies_trivial_sound.
    + move: Hc => /(@Forall_inv _ _ _). naive_solver.
  - destruct (regcol_cancel regs1 regs2) as [[??]?] eqn:?; simplify_eq/=.
    iDestruct ("IH" with "[//] [//] Hregs1") as "[? H2]" => /=. iFrame.
    rewrite !reg_col_cons. iIntros "[$ ?]". by iApply "H2".
Qed.

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac normalize_hook ::=
  autorewrite with isla_coq_rewrite; exact: eq_refl.
(* Ltac normalize_hook ::= normalize_autorewrite. *)

Ltac bv_solve_unfold_tac ::= idtac.

Ltac solve_protected_eq_hook ::=
  reduce_closed_N.

(* injection on bitvectors sometimes creates weird matches, so we disable it. *)
Ltac check_injection_hook ::=
  lazymatch goal with
  | |- @eq (bv _) _ _ → _ => fail
  | |- _ => idtac
  end.

(* TODO: enable liToSyntax *)
Ltac liToSyntax_hook ::= fail.

Ltac prepare_sidecond :=
  unshelve_sidecond; unLET; normalize_and_simpl_goal => //=.

Definition let_bind_hint {A B} (x : A) (f : A → B) : B :=
  f x.

Inductive instr_kind {Σ} : Type :=
| IKInstr (ins : option isla_trace) | IKPre (l : bool) (P : iProp Σ).
Definition FindInstrKind {Σ} `{!Arch} `{!islaG Σ} `{!threadG} (a : Z) (l : bool) := {|
  fic_A := @instr_kind Σ;
  fic_Prop ik :=
    match ik with
    | IKInstr ins => instr a ins
    | IKPre l' P => instr_pre' l' a P
    end
|}.
Global Typeclasses Opaque FindInstrKind.

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
Global Typeclasses Opaque FindRegMapsTo.
Definition FindStructRegMapsTo {Σ} `{!islaG Σ} `{!threadG} (r f : string) := {|
  fic_A := reg_mapsto_kind;
  fic_Prop rk :=
  match rk with
  | RKMapsTo v => (r # f ↦ᵣ v)%I
  | RKCol regs => reg_col regs
  end
|}.
Global Typeclasses Opaque FindStructRegMapsTo.

Inductive mem_mapsto_kind : Type :=
| MKMapsTo (n : N) (v : bv n)
| MKArray (n : N) (a : Z) (l : list (bv n))
| MKUninit (a : Z) (n : Z)
| MKMMIO (a : Z) (l : Z).
Definition mem_mapsto_kind_prop `{!islaG Σ} (a : Z) (mk : mem_mapsto_kind) : iProp Σ :=
  match mk with
  | MKMapsTo _ v => (a ↦ₘ v)%I
  | MKArray _ a' l => (a' ↦ₘ∗ l)%I
  | MKUninit a' n => (a' ↦ₘ? n)%I
  | MKMMIO a' l => mmio_range a' l
  end.
Global Typeclasses Opaque mem_mapsto_kind_prop.
Definition FindMemMapsTo {Σ} `{!islaG Σ} (a : Z) := {|
  fic_A := mem_mapsto_kind;
  fic_Prop := mem_mapsto_kind_prop a
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
    (∃ P, instr_pre' false a P ∗ T (IKPre false P))
    ⊢ find_in_context (FindInstrKind a false) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Definition find_in_context_instr_kind_pre_false_inst :=
    [instance find_in_context_instr_kind_pre_false with FICSyntactic].
  Global Existing Instance find_in_context_instr_kind_pre_false_inst | 1.

  Lemma find_in_context_instr_kind_pre_true a T:
    (∃ l P, instr_pre' l a P ∗ T (IKPre l P))
    ⊢ find_in_context (FindInstrKind a true) T.
  Proof. iDestruct 1 as (??) "[??]". iExists _. by iFrame. Qed.
  Definition find_in_context_instr_kind_pre_true_inst :=
    [instance find_in_context_instr_kind_pre_true with FICSyntactic].
  Global Existing Instance find_in_context_instr_kind_pre_true_inst | 1.

  Lemma find_in_context_instr_kind_instr a l T:
    (∃ ins, instr a ins ∗ T (IKInstr ins))
    ⊢ find_in_context (FindInstrKind a l) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Definition find_in_context_instr_kind_instr_inst :=
    [instance find_in_context_instr_kind_instr with FICSyntactic].
  Global Existing Instance find_in_context_instr_kind_instr_inst | 10.

  Inductive FICInstrSemantic : Set :=.
  Definition find_in_context_instr_pre_semantic_false_inst :=
    [instance find_in_context_instr_kind_pre_false with FICInstrSemantic].
  Global Existing Instance find_in_context_instr_pre_semantic_false_inst | 100.
  Definition find_in_context_instr_pre_semantic_true_inst :=
    [instance find_in_context_instr_kind_pre_true with FICInstrSemantic].
  Global Existing Instance find_in_context_instr_pre_semantic_true_inst | 100.

  Definition find_in_context_instr_semantic_inst :=
    [instance find_in_context_instr_kind_instr with FICInstrSemantic].
  Global Existing Instance find_in_context_instr_semantic_inst | 110.

  Global Instance mem_related A a n (v : A → bv n) : RelatedTo (λ x, a ↦ₘ (v x))%I := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Global Instance mem_array_related A a n (l : A → list (bv n)) : RelatedTo (λ x, a ↦ₘ∗ l x)%I := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Global Instance mem_uninit_related A a n : RelatedTo (λ x : A, a ↦ₘ? n x)%I := {|
    rt_fic := FindMemMapsTo a;
  |}.

  Lemma find_in_context_mem_mapsto_id a T:
    (∃ n (v : bv n), a ↦ₘ v ∗ T (MKMapsTo n v))
    ⊢ find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (? v) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Definition find_in_context_mem_mapsto_id_inst :=
    [instance find_in_context_mem_mapsto_id with FICSyntactic].
  Global Existing Instance find_in_context_mem_mapsto_id_inst | 1.

  Inductive FICMemMapstoSemantic (a : Z) : Set :=.
  Lemma find_in_context_mem_mapsto_semantic a T:
    (∃ mk, mem_mapsto_kind_prop a mk ∗ T mk)
    ⊢ find_in_context (FindMemMapsTo a) T.
  Proof. iDestruct 1 as (?) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Definition find_in_context_mem_mapsto_semantic_inst a :=
    [instance find_in_context_mem_mapsto_semantic a with FICMemMapstoSemantic a].
  Global Existing Instance find_in_context_mem_mapsto_semantic_inst | 10.

  Global Instance reg_related A r v : RelatedTo (λ x : A, r ↦ᵣ v x)%I := {|
    rt_fic := FindRegMapsTo r;
  |}.
  Global Instance struct_reg_related A r f v : RelatedTo (λ x : A, r # f ↦ᵣ v x)%I := {|
    rt_fic := FindStructRegMapsTo r f;
  |}.

  Global Instance reg_col_reg_related A r s rs : RelatedTo (λ x : A, reg_col ((KindReg r, s x)::rs x)) := {|
    rt_fic := FindRegMapsTo r;
  |}.
  Global Instance reg_col_struct_reg_related A r f s rs : RelatedTo (λ x : A, reg_col ((KindField r f, s x)::rs x)) := {|
    rt_fic := FindStructRegMapsTo r f;
  |}.

  Global Instance reg_pred_related A r P : RelatedTo (λ x : A, r ↦ᵣ: P x)%I := {|
    rt_fic := FindRegMapsTo r;
  |}.
  Global Instance struct_reg_pred_related A r f P : RelatedTo (λ x : A, r # f ↦ᵣ: P x)%I := {|
    rt_fic := FindStructRegMapsTo r f;
  |}.

  Lemma find_in_context_reg_mapsto r T:
    (∃ v, r ↦ᵣ v ∗ T (RKMapsTo v))
    ⊢ find_in_context (FindRegMapsTo r) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Definition find_in_context_reg_mapsto_inst :=
    [instance find_in_context_reg_mapsto with FICSyntactic].
  Global Existing Instance find_in_context_reg_mapsto_inst | 1.

  Lemma find_in_context_reg_mapsto_col r T:
    (∃ regs, reg_col regs ∗ T (RKCol regs))
    ⊢ find_in_context (FindRegMapsTo r) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Inductive FICRegMapstoSemantic (r : string) : Set :=.
  Definition find_in_context_reg_mapsto_col_inst r :=
    [instance find_in_context_reg_mapsto_col r with FICRegMapstoSemantic r].
  Global Existing Instance find_in_context_reg_mapsto_col_inst | 10.

  Lemma find_in_context_struct_reg_mapsto r f T:
    (∃ v, r # f ↦ᵣ v ∗ T (RKMapsTo v))
    ⊢ find_in_context (FindStructRegMapsTo r f) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Definition find_in_context_struct_reg_mapsto_inst :=
    [instance find_in_context_struct_reg_mapsto with FICSyntactic].
  Global Existing Instance find_in_context_struct_reg_mapsto_inst | 1.

  Lemma find_in_context_struct_reg_mapsto_col r f T:
    (∃ regs, reg_col regs ∗ T (RKCol regs))
    ⊢ find_in_context (FindStructRegMapsTo r f) T.
  Proof. iDestruct 1 as (?) "[??]". iExists _. by iFrame. Qed.
  Inductive FICStructRegMapstoSemantic (r f : string) : Set :=.
  Definition find_in_context_struct_reg_mapsto_col_inst r f :=
    [instance find_in_context_struct_reg_mapsto_col r f with FICStructRegMapstoSemantic r f].
  Global Existing Instance find_in_context_struct_reg_mapsto_col_inst | 10.

  Global Instance instr_related A a i : RelatedTo (λ x : A, instr a (i x)) := {|
    rt_fic := FindDirect (λ i, instr a i)%I;
  |}.

  Global Instance instr_pre'_related A b a P : RelatedTo (λ x : A, instr_pre' b a (P x)) := {|
    rt_fic := FindInstrKind a b;
  |}.

  Global Instance spec_trace_related A κs : RelatedTo (λ x : A, spec_trace (κs x)) := {|
    rt_fic := FindDirect (λ κs, spec_trace κs)%I;
  |}.

  Lemma subsume_reg A r v1 v2 G:
    (∃ x, ⌜v1 = v2 x⌝ ∗ G x)
    ⊢ subsume (r ↦ᵣ v1) (λ x : A, r ↦ᵣ v2 x) G.
  Proof. iDestruct 1 as (?->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_reg_inst := [instance subsume_reg].
  Global Existing Instance subsume_reg_inst.

  Lemma subsume_struct_reg A r f v1 v2 G:
    (∃ x, ⌜v1 = v2 x⌝ ∗ G x)
    ⊢ subsume (r # f ↦ᵣ v1) (λ x : A, r # f ↦ᵣ v2 x) G.
  Proof. iDestruct 1 as (?->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_struct_reg_inst := [instance subsume_struct_reg].
  Global Existing Instance subsume_struct_reg_inst.

  Lemma subsume_regcol_reg A regs r v G:
    (li_tactic (regcol_compute_hint (regcol_extract (KindReg r)) regs) (λ '(s, regs'),
      ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ ∃ x, ⌜v x = v'⌝ ∗ G x))
    ⊢ subsume (reg_col regs) (λ x : A, r ↦ᵣ v x) G.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as ([??] ?) "HG"; simplify_eq/=. iIntros "Hr".
    iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
    iDestruct ("HG" with "[//] Hregs") as (?) "[% HG]"; simplify_eq/=. iExists _. by iFrame.
  Qed.
  Definition subsume_regcol_reg_inst := [instance subsume_regcol_reg].
  Global Existing Instance subsume_regcol_reg_inst.

  Lemma subsume_struct_regcol_reg A regs r f v G:
    (li_tactic (regcol_compute_hint (regcol_extract (KindField r f)) regs) (λ '(s, regs'),
      ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ ∃ x, ⌜v x = v'⌝ ∗ G x))
    ⊢ subsume (reg_col regs) (λ x : A, r # f ↦ᵣ v x) G.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as ([??] ?) "HG"; simplify_eq/=. iIntros "Hr".
    iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
    iDestruct ("HG" with "[//] Hregs") as (?) "[% HG]"; simplify_eq/=. iExists _. by iFrame.
  Qed.
  Definition subsume_struct_regcol_reg_inst := [instance subsume_struct_regcol_reg].
  Global Existing Instance subsume_struct_regcol_reg_inst.

  Lemma subsume_reg_regcol A regs r v s G:
    (∃ x, ⌜valu_has_shape v (s x)⌝ ∗ reg_col (regs x) ∗ G x)
    ⊢ subsume (r ↦ᵣ v) (λ x : A, reg_col ((KindReg r, s x)::regs x)) G.
  Proof. iIntros "[% [% [Hregs ?]]] Hr". iExists _. rewrite reg_col_cons. eauto with iFrame. Qed.
  Definition subsume_reg_regcol_inst := [instance subsume_reg_regcol].
  Global Existing Instance subsume_reg_regcol_inst.
  Lemma subsume_struct_reg_regcol A regs r f v s G:
    (∃ x, ⌜valu_has_shape v (s x)⌝ ∗ reg_col (regs x) ∗ G x)
    ⊢ subsume (r # f ↦ᵣ v) (λ x : A, reg_col ((KindField r f, s x)::regs x)) G.
  Proof. iIntros "[% [% [Hregs ?]]] Hr". iExists _. rewrite reg_col_cons. eauto with iFrame. Qed.
  Definition subsume_struct_reg_regcol_inst := [instance subsume_struct_reg_regcol].
  Global Existing Instance subsume_struct_reg_regcol_inst.

  Lemma subsume_regcol_regcol A regs1 regs2 G:
    (li_tactic (regcol_compute_hint (λ '(regs1, regs2), Some (regcol_cancel regs1 regs2)) (regs1, regs2))
                 (λ '(regs1', regs2', c),
       ⌜foldr (λ c, and (valu_shape_implies c.1 c.2)) True c⌝ ∗
       (reg_col regs1' -∗ ∃ x, reg_col regs2' ∗ G x)))
    ⊢ subsume (reg_col regs1) (λ x : A, reg_col regs2) G.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as ([[regs1' regs2'] c] [=] Hf) "HT". move/Forall_fold_right in Hf.
    iIntros "Hregs".
    iDestruct (regcol_cancel_sound with "Hregs") as "[? H2]"; [done| |] => /=.
    { apply: Forall_impl; [done|] => /= ????. by apply: valu_shape_implies_sound; [|done]. }
    iDestruct ("HT" with "[$]") as (?) "[? ?]". iExists _. iFrame. by iApply "H2".
  Qed.
  Definition subsume_regcol_regcol_inst := [instance subsume_regcol_regcol].
  Global Existing Instance subsume_regcol_regcol_inst.

  Lemma subsume_reg_reg_pred A r v P G:
    (∃ x, P x v ∗ G x)
    ⊢ subsume (r ↦ᵣ v) (λ x : A, r ↦ᵣ: P x) G.
  Proof. iIntros "[% [? ?]] ?". iExists _. iFrame. rewrite reg_mapsto_pred_eq. iExists _. iFrame. Qed.
  Definition subsume_reg_reg_pred_inst := [instance subsume_reg_reg_pred].
  Global Existing Instance subsume_reg_reg_pred_inst.

  Lemma subsume_struct_reg_reg_pred A r f v P G:
    (∃ x, P x v ∗ G x)
    ⊢ subsume (r # f ↦ᵣ v) (λ x : A, r # f ↦ᵣ: P x) G.
  Proof. iIntros "[% [? ?]] ?". iExists _. iFrame. rewrite struct_reg_mapsto_pred_eq. iExists _. iFrame. Qed.
  Definition subsume_struct_reg_reg_pred_inst := [instance subsume_struct_reg_reg_pred].
  Global Existing Instance subsume_struct_reg_reg_pred_inst.

  Lemma subsume_regcol_reg_pred A regs r P G:
    (li_tactic (regcol_compute_hint (regcol_extract (KindReg r)) regs) (λ '(s, regs'),
      ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ ∃ x, P x v' ∗ G x))
    ⊢ subsume (reg_col regs) (λ x : A, r ↦ᵣ: P x) G.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as ([??] ?) "HG"; simplify_eq/=. iIntros "Hr".
    iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
    iDestruct ("HG" with "[//] Hregs") as (?) "[? HG]"; simplify_eq/=.
    iExists _. iFrame. rewrite reg_mapsto_pred_eq. iExists _. by iFrame.
  Qed.
  Definition subsume_regcol_reg_pred_inst := [instance subsume_regcol_reg_pred].
  Global Existing Instance subsume_regcol_reg_pred_inst.

  Lemma subsume_struct_regcol_reg_pred A regs r f P G:
    (li_tactic (regcol_compute_hint (regcol_extract (KindField r f)) regs) (λ '(s, regs'),
      ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ ∃ x, P x v' ∗ G x))
    ⊢ subsume (reg_col regs) (λ x : A, r # f ↦ᵣ: P x) G.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as ([??] ?) "HG"; simplify_eq/=. iIntros "Hr".
    iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
    iDestruct ("HG" with "[//] Hregs") as (?) "[? HG]"; simplify_eq/=. iExists _. iFrame.
    rewrite struct_reg_mapsto_pred_eq. iExists _. by iFrame.
  Qed.
  Definition subsume_struct_regcol_reg_pred_inst := [instance subsume_struct_regcol_reg_pred].
  Global Existing Instance subsume_struct_regcol_reg_pred_inst.

  Lemma reg_mapsto_pred_ex {A B} r (P : (A *ₗ B) → _ → _) :
    r ↦ᵣ: (λ y, ∃ₗ x, P x y)
    ⊢ ∃ₗ x, r ↦ᵣ: (P x).
  Proof.
    rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iIntros "(%&?&%&?)". iExists _, _. iFrame.
  Qed.

  Lemma reg_mapsto_pred_intro r P :
    find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v => P v
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_extract (KindReg r)) regs) (λ '(s, regs'),
            ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ P v'))
      end)
    ⊢ r ↦ᵣ: P.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - eauto with iFrame.
    - iDestruct "Hwp" as ([??] ?) "HG"; simplify_eq/=.
      iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
      iDestruct ("HG" with "[//] Hregs") as "HG"; simplify_eq/=. iExists _. by iFrame.
  Qed.

  Lemma struct_reg_mapsto_pred_intro r f P :
    find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v => P v
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_extract (KindField r f)) regs) (λ '(s, regs'),
            ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs' -∗ P v'))
      end)
    ⊢ r # f ↦ᵣ: P.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    rewrite struct_reg_mapsto_pred_eq /struct_reg_mapsto_pred_def.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - eauto with iFrame.
    - iDestruct "Hwp" as ([??] ?) "HG"; simplify_eq/=.
      iDestruct (regcol_extract_Some with "Hr") as (??) "[? Hregs]"; [done|] => /=.
      iDestruct ("HG" with "[//] Hregs") as "HG"; simplify_eq/=. iExists _. by iFrame.
  Qed.

  Lemma simpl_hyp_reg_pred r P G:
    (∀ v, r ↦ᵣ v -∗ P v -∗ G)
    ⊢ simplify_hyp (r ↦ᵣ: P) G.
  Proof.
    rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iIntros "HG [%v [? ?]]". by iApply ("HG" with "[$]").
  Qed.
  Definition simpl_hyp_reg_pred_inst := [instance simpl_hyp_reg_pred with 0%N].
  Global Existing Instance simpl_hyp_reg_pred_inst.

  Lemma simpl_hyp_struct_reg_pred r f P G:
    (∀ v, r # f ↦ᵣ v -∗ P v -∗ G)
    ⊢ simplify_hyp (r # f ↦ᵣ: P) G.
  Proof.
    rewrite struct_reg_mapsto_pred_eq /struct_reg_mapsto_pred_def.
    iIntros "HG [%v [? ?]]". by iApply ("HG" with "[$]").
  Qed.
  Definition simpl_hyp_struct_reg_pred_inst := [instance simpl_hyp_struct_reg_pred with 0%N].
  Global Existing Instance simpl_hyp_struct_reg_pred_inst.

  Lemma subsume_instr A a i1 i2 G:
    (∃ x, ⌜i1 = i2 x⌝ ∗ G x)
    ⊢ subsume (instr a i1) (λ x : A, instr a (i2 x)) G.
  Proof. iDestruct 1 as (? ->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_instr_inst := [instance subsume_instr].
  Global Existing Instance subsume_instr_inst.

  Lemma subsume_instr_pre' A a b1 b2 P1 P2 G:
    (∃ x, ⌜b1 = b2 x⌝ ∗ ⌜P1 = P2 x⌝ ∗ G x)
    ⊢ subsume (instr_pre' b1 a P1) (λ x : A, instr_pre' (b2 x) a (P2 x)) G.
  Proof. iDestruct 1 as (? -> ->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_instr_pre'_inst := [instance subsume_instr_pre'].
  Global Existing Instance subsume_instr_pre'_inst.

  Lemma subsume_spec_trace_ex A Pκs1 Pκs2 G `{!∀ x, IsEx (Pκs2 x)}:
    (∃ x, ⌜Pκs1 = Pκs2 x⌝ ∗ G x)
    ⊢ subsume (spec_trace Pκs1) (λ x : A, spec_trace (Pκs2 x)) G.
  Proof. iDestruct 1 as (? ->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_spec_trace_ex_inst := [instance subsume_spec_trace_ex].
  Global Existing Instance subsume_spec_trace_ex_inst | 10.

  Lemma subsume_spec_trace A Pκs1 Pκs2 G:
    (∃ x, ⌜Pκs2 x ⊆ Pκs1⌝ ∗ G x)
    ⊢ subsume (spec_trace Pκs1) (λ x : A, spec_trace (Pκs2 x)) G.
  Proof. iDestruct 1 as (??) "?". iIntros "?". iExists _. iFrame. by iApply spec_trace_mono. Qed.
  Definition subsume_spec_trace_inst := [instance subsume_spec_trace].
  Global Existing Instance subsume_spec_trace_inst | 50.

  Lemma subsume_mem A a n (v1 : bv n) (v2 : A → bv n) G:
    (∃ x, ⌜v1 = v2 x⌝ ∗ G x)
    ⊢ subsume (a ↦ₘ v1) (λ x : A, a ↦ₘ v2 x) G.
  Proof. iDestruct 1 as (? ->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_mem_inst := [instance subsume_mem].
  Global Existing Instance subsume_mem_inst.

  Lemma subsume_mem_array A a1 a2 n (l1 : list (bv n)) (l2 : A → list (bv n)) G:
    (∃ x, ⌜a1 = a2⌝ ∗ ⌜l1 = l2 x⌝ ∗ G x)
    ⊢ subsume (a1 ↦ₘ∗ l1) (λ x : A, a2 ↦ₘ∗ (l2 x)) G.
  Proof. iDestruct 1 as (? -> ->) "?". iIntros "?". iExists _. iFrame. Qed.
  Definition subsume_mem_array_inst := [instance subsume_mem_array].
  Global Existing Instance subsume_mem_array_inst.

  (* This handles the case where the goal is fully contained in the hypthesis. I.e.
     |------ hyp ------|
          |-- goal --|
  *)
  Lemma subsume_mem_uninit_mem_uninit A a1 a2 n1 n2 G
        `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 + n2 ≤ a1 + n1)}:
    (li_tactic (normalize_bv_wrap (a2 - a1)) (λ m1, ⌜0 ≤ m1 < 2 ^ 64⌝ ∗
     li_tactic (normalize_bv_wrap (n1 - n2 - m1)) (λ m2, ⌜0 ≤ m2 < 2 ^ 64 ∧ n1 < 2 ^ 64⌝ ∗ (
      a1 ↦ₘ? m1 -∗
     (a2 + n2) ↦ₘ? m2 -∗ ∃ x, G x))))
    ⊢ subsume (a1 ↦ₘ? n1) (λ x : A, a2 ↦ₘ? n2) G.
  Proof.
    unfold BvSolve, normalize_bv_wrap, li_tactic in *. iIntros "HG Ha".
    iDestruct "HG" as "(%m1&%Hm1&%&%m2&%Hm2&%&HG)".
    iDestruct (mem_mapsto_uninit_split m1 with "Ha") as "[? Ha]"; [bv_solve|].
    iDestruct (mem_mapsto_uninit_split n2 with "Ha") as "[? Ha]"; [bv_solve|].
    have -> : a1 + m1 = a2 by bv_solve.
    have -> : (n1 - m1 - n2) = m2 by bv_solve.
    iFrame. iApply ("HG" with "[$] [$]").
  Qed.
  Definition subsume_mem_uninit_mem_uninit_inst := [instance subsume_mem_uninit_mem_uninit].
  Global Existing Instance subsume_mem_uninit_mem_uninit_inst.

  (* This handles the case where the kypothesis does not fully containe the goal. I.e.
     |--- hyp ---|
          |-- goal --|
   *)
  (* This rule breaks if one of the uninit spans 2^64 bytes but that seems quite rare. *)
  Lemma subsume_mem_uninit_mem_uninit2 A a1 a2 n1 n2 G
        `{!BvSolve (0 ≤ n2 ∧ a1 ≤ a2 ∧ a2 ≤ a1 + n1 ∧ a1 + n1 ≤ a2 + n2)}:
    (li_tactic (normalize_bv_wrap (a2 - a1)) (λ m1, ⌜0 ≤ m1 < 2 ^ 64⌝ ∗
     li_tactic (normalize_bv_wrap (n2 - (n1 - m1))) (λ m2, ⌜0 ≤ m2 < 2 ^ 64⌝ ∗
     li_tactic (normalize_bv_wrap (a2 + n1 - m1)) (λ m3, ⌜a2 + n2 < 2 ^ 64 ∧ m3 + m2 < 2 ^ 64⌝ ∗ (
     a1 ↦ₘ? m1 -∗
     m3 ↦ₘ? m2 ∗ ∃ x, G x)))))
    ⊢ subsume (a1 ↦ₘ? n1) (λ x : A, a2 ↦ₘ? n2) G.
  Proof.
    unfold BvSolve, normalize_bv_wrap, li_tactic in *. iIntros "HG Ha".
    iDestruct "HG" as "(%m1&%Hm1&%&%m2&%Hm2&%&%m3&%Hm3&%&HG)".
    iDestruct (mem_mapsto_uninit_in_range with "Ha") as %?.
    iDestruct (mem_mapsto_uninit_split m1 with "Ha") as "[? Ha]"; [bv_solve|].
    iDestruct ("HG" with "[$]") as "[H1 [% ?]]". iExists _. iFrame.
    have -> : a1 + m1 = a2 by bv_solve.
    iApply (mem_mapsto_uninit_combine with "Ha"); [bv_solve|].
    iDestruct (mem_mapsto_uninit_in_range with "H1") as %?.
    have -> : (a2 + (n1 - m1)) = m3 by bv_solve.
    by have -> : (n2 - (n1 - m1)) = m2 by bv_solve.
  Qed.
  Definition subsume_mem_uninit_mem_uninit2_inst := [instance subsume_mem_uninit_mem_uninit2].
  Global Existing Instance subsume_mem_uninit_mem_uninit2_inst.

  (* This rule breaks if one of the uninit spans 2^64 bytes but that seems quite rare. *)
  Lemma subsume_mem_mapsto_mem_uninit A a1 a2 n (b : bv n) n2 G:
    (⌜a1 = a2⌝ ∗ ⌜Z.of_N (n `div` 8) ≤ n2⌝ ∗
    (a2 + (Z.of_N (n `div` 8))) ↦ₘ? (n2 - (Z.of_N (n `div` 8))) ∗ ∃ x, G x)
    ⊢ subsume (a1 ↦ₘ b) (λ x : A, a2 ↦ₘ? n2) G.
  Proof.
    iIntros "[-> [% [Ha2 [% ?]]]] Ha". iExists _. iFrame.
    iDestruct (mem_mapsto_n_mult_8 with "Ha") as %[n' ?]; subst.
    iDestruct (mem_mapsto_mapsto_to_uninit with "Ha") as "Ha".
    by iApply (mem_mapsto_uninit_combine with "Ha"); [bv_solve|].
  Qed.
  Definition subsume_mem_mapsto_mem_uninit_inst := [instance subsume_mem_mapsto_mem_uninit].
  Global Existing Instance subsume_mem_mapsto_mem_uninit_inst.

  Lemma simpl_hyp_uninit_0 a n G `{!BvSolve (n = 0)}:
    G
    ⊢ simplify_hyp (a ↦ₘ? n) G.
  Proof. by iIntros "$ ?". Qed.
  Definition simpl_hyp_uninit_0_inst := [instance simpl_hyp_uninit_0 with 0%N].
  Global Existing Instance simpl_hyp_uninit_0_inst.

  Lemma simpl_goal_uninit_0 a n G `{!BvSolve (n = 0)}:
    ⌜0 ≤ a ≤ 2 ^ 64⌝ ∗ G
    ⊢ simplify_goal (a ↦ₘ? n) G.
  Proof.
    unfold BvSolve in *. subst. iIntros "[% $]". by rewrite mem_mapsto_uninit_0.
  Qed.
  Definition simpl_goal_uninit_0_inst := [instance simpl_goal_uninit_0 with 0%N].
  Global Existing Instance simpl_goal_uninit_0_inst.

  Lemma simpl_goal_reg_col_nil T:
    T
    ⊢ simplify_goal (reg_col []) T.
  Proof. iIntros "$". by rewrite reg_col_nil. Qed.
  Definition simpl_goal_reg_col_nil_inst := [instance simpl_goal_reg_col_nil with 100%N].
  Global Existing Instance simpl_goal_reg_col_nil_inst.

  Lemma li_wp_next_instr:
    (∃ (nPC : addr),
     arch_pc_reg ↦ᵣ RVal_Bits nPC ∗
     li_tactic (normalize_instr_addr (bv_unsigned nPC)) (λ normPC,
     let newPC := Z_to_bv 64 normPC in
     find_in_context (FindInstrKind normPC true) (λ ik,
     match ik with
     | IKInstr (Some t) => arch_pc_reg ↦ᵣ RVal_Bits newPC -∗ WPasm t
     | IKInstr (None) =>
       ∃ Pκs, spec_trace Pκs ∗ ⌜scons (SInstrTrap newPC) snil ⊆ Pκs⌝ ∗ True
     | IKPre l P => P
     end
    )))
    ⊢ WPasm tnil.
  Proof.
    unfold normalize_instr_addr. iDestruct 1 as (?) "(HPC&%normPC&%Hnorm&Hwp)".
    have ? := bv_unsigned_in_range _ nPC.
    iDestruct "Hwp" as (ins) "[Hi Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct (instr_addr_in_range with "Hi") as %?.
      rewrite !bv_wrap_small // in Hnorm. subst.
      iApply (wp_next_instr with "HPC Hi") => //.
      iIntros "!> ?". rewrite Z_to_bv_bv_unsigned.
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
    (li_tactic (normalize_instr_addr a) (λ normPC,
     let newPC := Z_to_bv 64 normPC in
     find_in_context (FindInstrKind normPC l) (λ ik,
     match ik with
     | IKInstr (Some t) =>
       P -∗ arch_pc_reg ↦ᵣ RVal_Bits newPC -∗ WPasm t
     | IKInstr None =>
       P -∗ ∃ Pκs, spec_trace Pκs ∗ ⌜scons (SInstrTrap newPC) snil ⊆ Pκs⌝ ∗ True
     | IKPre l' Q => ⌜implb l' l⌝ ∗ (P -∗ Q)
     end
    )))
    ⊢ instr_pre' l a P.
  Proof.
    unfold normalize_instr_addr.  iDestruct 1 as (normPC Hnorm ins) "[Hinstr Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct (instr_addr_in_range with "Hinstr") as %?.
      rewrite (bv_wrap_small _ normPC) // in Hnorm. subst.
      iApply (instr_pre_wand with "[-]"); [by erewrite implb_same| | | iIntros "HP"; iApply "HP"].
      2: by iApply (instr_pre_intro_Some with "[$]"); [done..|].
      by rewrite bv_wrap_bv_wrap.
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

  Lemma li_wp_cases ts:
    (⌜ts ≠ []⌝ ∗ [∧ list] t ∈ ts, WPasm t)
    ⊢ WPasm (tcases ts).
  Proof.
    iIntros "[% Hwp]". iApply wp_cases; [done|].
    iIntros (t Ht). by iApply (big_andL_elem_of with "Hwp").
  Qed.

  Lemma li_wpreadreg_nil r Φ:
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => r ↦ᵣ v' -∗ Φ v'
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_lookup (KindReg r)) regs) (λ '(_, s),
             ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs -∗ Φ v'))
      end))
    ⊢ WPreadreg r @ [] {{ Φ }}.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (read_reg_nil with "Hr").
    - iDestruct "Hwp" as ([??] ?%regcol_lookup_Some) "Hwp"; simplify_eq/=.
      iDestruct (reg_col_lookup with "Hr") as (vact ?) "[Hr Hregs]"; [done|] => /=.
      iApply (read_reg_nil with "Hr").  iIntros "Hr". iApply "Hwp"; [done|].
      iApply reg_col_lookup; [done|]. iExists _. by iFrame.
  Qed.

  Lemma li_wpreadreg_field r f Φ:
    (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => r # f ↦ᵣ v' -∗ Φ v'
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_lookup_field r f) regs) (λ '(_, s),
             ∀ v', ⌜valu_has_shape v' s⌝ -∗ reg_col regs -∗ Φ v'))
      end))
    ⊢ WPreadreg r @ [Field f] {{ Φ }}.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (read_reg_struct with "Hr").
    - iDestruct "Hwp" as ([b s] Hs) "Hwp"; simplify_eq/=.
      iDestruct (regcol_lookup_field_Some with "Hr") as (???) "[Hr Hregs]"; [done|] => /=.
      destruct b.
      + iApply (read_reg_struct with "Hr"). iIntros "Hr". iApply ("Hwp" with "[//]"). by iApply "Hregs".
      + iDestruct "Hr" as "[Hr %]". iApply (read_reg_acc with "Hr"); [done..|].
        iIntros "Hr". iApply ("Hwp" with "[//]"). iApply "Hregs". by iFrame.
  Qed.

  Lemma li_wp_read_reg r v ann es :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜v = v'⌝ -∗ r ↦ᵣ v' -∗ WPasm es)
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_lookup (KindReg r)) regs) (λ '(_, s),
             reg_col regs -∗ ⌜valu_has_shape v s⌝ -∗ WPasm es))
      end))
    ⊢ WPasm (ReadReg r [] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hrk HG]". iApply wp_read_reg; [done|].
    iApply li_wpreadreg_nil. iExists _. iFrame. destruct rk => /=.
    - iIntros "? %". by iApply "HG".
    - iDestruct "HG" as ([??]?) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "? %". subst. by iApply ("HG" with "[$]").
  Qed.

  Lemma li_wp_read_reg_struct r f v ann es :
    (∃ vread, ⌜read_accessor [Field f] v = Some vread⌝ ∗
     (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜vread = v'⌝ -∗ r # f ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => li_tactic (regcol_compute_hint (regcol_lookup_field r f) regs) (λ '(b, s),
             ⌜valu_has_shape vread s⌝ -∗ reg_col regs -∗ WPasm es)
      end)))
    ⊢ WPasm (ReadReg r [Field f] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (vread ? rk) "[Hrk HG]". iApply wp_read_reg; [done|].
    iApply li_wpreadreg_field. iExists _. iFrame. destruct rk => /=.
    - iIntros "? %". by iApply "HG".
    - iDestruct "HG" as ([??]?) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "? %". subst. by iApply ("HG" with "[] [$]").
  Qed.

  Lemma li_wp_assume_reg r v ann es :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜v = v'⌝ ∗ (r ↦ᵣ v' -∗ WPasm es))
      | RKCol regs =>
          (li_tactic (regcol_compute_hint (regcol_lookup (KindReg r)) regs) (λ '(_, s),
             ⌜∀ v', valu_has_shape v' s → v' = v⌝ ∗ (reg_col regs -∗ WPasm es)))
      end))
    ⊢ WPasm (AssumeReg r [] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hrk HG]". iApply wp_assume_reg.
    iApply li_wpreadreg_nil. iExists _. iFrame. destruct rk => /=.
    - iDestruct "HG" as (?) "HG". iIntros "?". iSplit; [done|]. by iApply "HG".
    - iDestruct "HG" as ([??]??) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "?". iSplit; [naive_solver|]. by iApply ("HG" with "[$]").
  Qed.

  Lemma li_wp_assume_reg_struct r f v ann es :
    ((find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => ⌜v = v'⌝ ∗ (r # f ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => li_tactic (regcol_compute_hint (regcol_lookup_field r f) regs) (λ '(b, s),
          if s is ExactShape v' then ⌜v = v'⌝ ∗ (reg_col regs -∗ WPasm es) else False)
      end)))
    ⊢ WPasm (AssumeReg r [Field f] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hrk HG]". iApply wp_assume_reg.
    iApply li_wpreadreg_field. iExists _. iFrame. destruct rk => /=.
    - iDestruct "HG" as (?) "HG". iIntros "?". iSplit; [done|]. by iApply "HG".
    - iDestruct "HG" as ([??]?) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "?". case_match => //. iDestruct "HG" as (?) "HG"; subst.
      iSplit; [naive_solver|]. by iApply ("HG" with "[$]").
  Qed.

  Lemma li_wp_write_reg r v ann es:
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (r ↦ᵣ v -∗ WPasm es)
      | RKCol regs =>
          (* We don't use regcol_extract here because it unfolds
          regs', which slows down the pKVM handler example quite a bit.
           TODO: find a more principled solution. *)
          (li_tactic (regcol_compute_hint (regcol_lookup (KindReg r)) regs) (λ '(i, s),
             r ↦ᵣ v -∗ reg_col (delete i regs) -∗ WPasm es))
      end))
    ⊢ WPasm (WriteReg r [] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_write_reg with "Hr").
    - iDestruct "Hwp" as ([??] ?%regcol_lookup_Some) "Hwp"; simplify_eq/=.
      iDestruct (reg_col_lookup with "Hr") as (??) "[Hr Hregs]"; [done|] => /=.
      iApply (wp_write_reg with "Hr"). iIntros "Hr". iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma li_wp_write_reg_struct r f v ann es:
    (∃ vnew, ⌜read_accessor [Field f] v = Some vnew⌝ ∗
    (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => (r # f ↦ᵣ vnew -∗ WPasm es)
      | RKCol regs =>
          (* We don't use regcol_extract here because it unfolds
          regs', which slows down the pKVM handler example quite a bit.
           TODO: find a more principled solution. *)
          (li_tactic (regcol_compute_hint (regcol_lookup (KindField r f)) regs) (λ '(i, s),
             r # f ↦ᵣ vnew -∗ reg_col (delete i regs) -∗ WPasm es))
      end)))
    ⊢ WPasm (WriteReg r [Field f] v ann :t: es).
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (vnew ? rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_write_reg_struct with "Hr").
    - iDestruct "Hwp" as ([??] ?%regcol_lookup_Some) "Hwp"; simplify_eq/=.
      iDestruct (reg_col_lookup with "Hr") as (??) "[Hr Hregs]"; [done|] => /=.
      iApply (wp_write_reg_struct with "Hr"); [done|]. iIntros "Hr". iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma li_wp_branch_address v ann es:
    WPasm es
    ⊢ WPasm (BranchAddress v ann :t: es).
  Proof. iApply wp_branch_address. Qed.

  Lemma li_wp_branch c desc ann es:
    WPasm es
    ⊢ WPasm (Branch c desc ann :t: es).
  Proof. iApply wp_branch. Qed.

  Lemma li_wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm (subst_trace (Val_Bits n) v es))
    ⊢ WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :t: es).
  Proof. iApply wp_declare_const_bv. Qed.

  Lemma li_wp_declare_const_bool v es ann:
    (∀ b : bool, WPasm (subst_trace (Val_Bool b) v es))
    ⊢ WPasm (Smt (DeclareConst v Ty_Bool) ann :t: es).
  Proof. iApply wp_declare_const_bool. Qed.

  Lemma li_wp_declare_const_enum v es i ann:
    (∀ c, WPasm (subst_trace (Val_Enum c) v es))
    ⊢ WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :t: es).
  Proof. iApply wp_declare_const_enum. Qed.

  Lemma li_wp_define_const n es ann e:
    li_tactic (compute_wp_exp e) (λ v, let_bind_hint v (λ v, WPasm (subst_trace v n es)))
    ⊢ WPasm (Smt (DefineConst n e) ann :t: es).
  Proof.
    iIntros "Hexp". iApply wp_define_const. unfold let_bind_hint.
    iApply (wpe_wand with "Hexp"). iIntros (?) "$".
  Qed.

  Lemma li_wp_assert es ann e:
    li_tactic (compute_wp_exp e) (λ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es))
    ⊢ WPasm (Smt (Assert e) ann :t: es).
  Proof. iApply wp_assert. Qed.

  Lemma li_wp_assume es ann e:
    WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ WPasm es }}
    ⊢ WPasm (Assume e ann :t: es).
  Proof. iApply wp_assume. Qed.

  Lemma li_wp_barrier es v ann:
    WPasm es
    ⊢ WPasm (Barrier v ann :t: es).
  Proof. iApply wp_barrier. Qed.

  Lemma li_wp_abstract_primop es n v args ann:
    WPasm es
    ⊢ WPasm (AbstractPrimop n v args ann :t: es).
  Proof. iApply wp_abstract_primop. Qed.

  Lemma li_wp_write_mem len n success kind a (vnew : bv n) tag ann es:
    (⌜n = (8*len)%N⌝ ∗
    ⌜len ≠ 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (λ mk,
      match mk with
      | MKMapsTo n' vold => ⌜n' = n⌝ ∗ (bv_unsigned a ↦ₘ vnew -∗ WPasm es)
      | MKArray n' a' l =>
        ⌜(bv_unsigned a - a') `mod` Z.of_N len = 0⌝ ∗
        ∃ i : nat, ⌜Z.of_nat i = (bv_unsigned a - a') / Z.of_N len⌝ ∗ ⌜i < length l⌝%nat ∗
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
    ))
    ⊢ WPasm (WriteMem (RVal_Bool success) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iDestruct 1 as (? ? mk) "[HP Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (->) "Hcont". iApply (wp_write_mem with "HP Hcont"); [done | lia].
    - iDestruct "Hcont" as (? i Heqi ? Heq) "Hcont". subst => /=. rename a0 into a'.
      have {} Heqi: a' = bv_unsigned a - i * Z.of_N len.
      { rewrite Heqi Z.mul_comm -Z_div_exact_full_2; [lia|lia|done]. }
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
      | MKArray n' a' l =>
        ⌜(bv_unsigned a - a') `mod` Z.of_N len = 0⌝ ∗
        ∃ i : nat, ⌜Z.of_nat i = (bv_unsigned a - a') / Z.of_N len⌝ ∗ ⌜i < length l⌝%nat ∗
        ∃ Heq : n = n', (∀ vmem, ⌜l !! i = Some vmem⌝ -∗ ⌜(eq_rect n bv vread n' Heq) = vmem⌝ -∗ a' ↦ₘ∗ l -∗ WPasm es)
      | MKUninit a' n' => False
      | MKMMIO a' l =>
        ⌜a' ≤ bv_unsigned a⌝ ∗ ⌜bv_unsigned a + Z.of_N len ≤ a' + l⌝ ∗
        ∃ Pκs Pκs', spec_trace Pκs ∗ ⌜scons (SReadMem a vread) Pκs' ⊆ Pκs⌝ ∗
        (spec_trace Pκs' -∗ WPasm es)
      end))
    ⊢ WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iDestruct 1 as (?? mk) "[Hmem Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (?) "Hcont". subst => /=. iApply (wp_read_mem with "Hmem Hcont"); [done|lia].
    - iDestruct "Hcont" as (? i Heqi [??]%lookup_lt_is_Some_2 ?) "Hcont". subst => /=.
      rename a0 into a'.
      have {} Heqi: a' = bv_unsigned a - i * Z.of_N len.
      { rewrite Heqi Z.mul_comm -Z_div_exact_full_2; [lia|lia|done]. }
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
    Φ v
    ⊢ WPexp (Val v ann) {{ Φ }}.
  Proof. iApply wpe_val. Qed.

  Lemma li_wpae_var_reg r Φ ann :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v => (if v is RegVal_Base v' then r ↦ᵣ v -∗ Φ v' else False)
      | RKCol regs =>
          li_tactic (regcol_compute_hint (regcol_lookup (KindReg r)) regs) (λ '(_, s),
           ∀ v, ⌜valu_has_shape v s⌝ -∗ ∃ v', ⌜v = RegVal_Base v'⌝ ∗ (reg_col regs -∗ Φ v')
             )
      end))
    ⊢ WPaexp (AExp_Val (AVal_Var r []) ann) {{ Φ }}.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hrk HG]". iApply wpae_var_reg.
    iApply li_wpreadreg_nil. iExists _. iFrame. destruct rk => /=.
    - by case_match.
    - iDestruct "HG" as ([??]?) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "?".
      iDestruct ("HG" with "[//]") as (??) "HG"; subst. by iApply "HG".
  Qed.

  Lemma li_wpae_var_struct r f Φ ann :
    (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v => (if v is RegVal_Base v' then r # f ↦ᵣ v -∗ Φ v' else False)
      | RKCol regs => li_tactic (regcol_compute_hint (regcol_lookup_field r f) regs) (λ '(b, s),
           ∀ v, ⌜valu_has_shape v s⌝ -∗ if v is RegVal_Base v' then (reg_col regs -∗ Φ v') else False)
      end))
    ⊢ WPaexp (AExp_Val (AVal_Var r [Field f]) ann) {{ Φ }}.
  Proof.
    unfold li_tactic, regcol_compute_hint.
    iDestruct 1 as (rk) "[Hrk HG]". iApply wpae_var_reg.
    iApply li_wpreadreg_field. iExists _. iFrame. destruct rk => /=.
    - by case_match.
    - iDestruct "HG" as ([??]?) "HG"; simplify_eq/=. unfold li_tactic, regcol_compute_hint.
      iExists (_, _). iSplit; [done|]. iIntros (??) "?".
      iDestruct ("HG" with "[//]") as "HG". case_match => //. by iApply "HG".
  Qed.

  Lemma li_wpae_bits b Φ ann:
    Φ (Val_Bits b)
    ⊢ WPaexp (AExp_Val (AVal_Bits b) ann) {{ Φ }}.
  Proof. iApply wpae_bits. Qed.
  Lemma li_wpae_bool b Φ ann:
    Φ (Val_Bool b)
    ⊢ WPaexp (AExp_Val (AVal_Bool b) ann) {{ Φ }}.
  Proof. iApply wpae_bool. Qed.
  Lemma li_wpae_enum b Φ ann:
    Φ (Val_Enum b)
    ⊢ WPaexp (AExp_Val (AVal_Enum b) ann) {{ Φ }}.
  Proof. iApply wpae_enum. Qed.

  Lemma li_wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es []
    ⊢ WPexp (Manyop op es ann) {{ Φ }}.
  Proof. iApply wpe_manyop. Qed.
  Lemma li_wpae_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPaexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es []
    ⊢ WPaexp (AExp_Manyop op es ann) {{ Φ }}.
  Proof. iApply wpae_manyop. Qed.

  Lemma li_wpe_unop op e Φ ann:
    WPexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}}
    ⊢ WPexp (Unop op e ann) {{ Φ }}.
  Proof. iApply wpe_unop. Qed.
  Lemma li_wpae_unop op e Φ ann:
    WPaexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}}
    ⊢ WPaexp (AExp_Unop op e ann) {{ Φ }}.
  Proof. iApply wpae_unop. Qed.

  Lemma li_wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }}
    ⊢ WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof. iApply wpe_binop. Qed.
  Lemma li_wpae_binop op e1 e2 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }}
    ⊢ WPaexp (AExp_Binop op e1 e2 ann) {{ Φ }}.
  Proof. iApply wpae_binop. Qed.

  Lemma li_wpe_ite e1 e2 e3 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, WPexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }}
    ⊢ WPexp (Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. iApply wpe_ite. Qed.
  Lemma li_wpae_ite e1 e2 e3 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, WPaexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }}
    ⊢ WPaexp (AExp_Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. iApply wpae_ite. Qed.
End instances.


Lemma tac_mem_mapsto_eq `{islaG Σ} l1 l' n (v1 : bv n) l2:
  l1 = l2 →
  FindHypEqual (FICMemMapstoSemantic l') (l1 ↦ₘ v1) (mem_mapsto_kind_prop l2 (MKMapsTo _ v1)) (l1 ↦ₘ v1).
Proof. by move => ->. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ _) (mem_mapsto_kind_prop _ _) _) =>
  ( apply tac_mem_mapsto_eq; bv_solve) : typeclass_instances.

Lemma tac_mem_mapsto_array_eq `{islaG Σ} a n a1 a2 (l1 : list (bv n)):
  a1 ≤ a < a1 + length l1 * Z.of_N (n `div` 8)%N
  ∨ a1 = a →
  FindHypEqual (FICMemMapstoSemantic a) (a1 ↦ₘ∗ l1) (mem_mapsto_kind_prop a2 (MKArray _ a1 l1)) (a1 ↦ₘ∗ l1).
Proof. done. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ∗ _) (mem_mapsto_kind_prop _ _) _) =>
  ( apply tac_mem_mapsto_array_eq; bv_solve) : typeclass_instances.

Lemma tac_mem_mapsto_uninit_eq `{islaG Σ} a a1 a2 n1:
  a1 ≤ a < a1 + n1 ∨ a1 = a →
  FindHypEqual (FICMemMapstoSemantic a) (a1 ↦ₘ? n1) (mem_mapsto_kind_prop a2 (MKUninit a1 n1)) (a1 ↦ₘ? n1).
Proof. done. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (_ ↦ₘ? _) (mem_mapsto_kind_prop _ _) _) =>
  ( apply tac_mem_mapsto_uninit_eq; bv_solve) : typeclass_instances.

Lemma tac_mem_mapsto_mmio `{islaG Σ} a a1 a2 l1:
  a1 ≤ a ≤ a1 + l1 →
  FindHypEqual (FICMemMapstoSemantic a) (mmio_range a1 l1) (mem_mapsto_kind_prop a2 (MKMMIO a1 l1)) (mmio_range a1 l1).
Proof. done. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _) (mmio_range _ _) (mem_mapsto_kind_prop _ _) _) =>
  ( apply tac_mem_mapsto_mmio; bv_solve) : typeclass_instances.

Lemma tac_reg_mapsto_reg_col `{islaG Σ} `{threadG} r regs1 regs2:
  is_Some (list_find_idx_bool (λ x, reg_kind_eqb x.1 (KindReg r)) regs1) →
  FindHypEqual (FICRegMapstoSemantic r) (reg_col regs1) (reg_col regs2) (reg_col regs2) .
Proof. done. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICRegMapstoSemantic _) (reg_col _) (reg_col _) _) =>
( apply tac_reg_mapsto_reg_col; vm_compute; eexists _; exact: eq_refl) : typeclass_instances.

Lemma tac_struct_reg_mapsto_reg_col `{islaG Σ} `{threadG} r f regs1 regs2:
  is_Some (list_find_idx_bool (λ x, reg_kind_eqb x.1 (KindField r f) || reg_kind_eqb x.1 (KindReg r)) regs1) →
  FindHypEqual (FICStructRegMapstoSemantic r f) (reg_col regs1) (reg_col regs2) (reg_col regs2) .
Proof. done. Qed.
#[ global ] Hint Extern 10 (FindHypEqual (FICStructRegMapstoSemantic _ _) (reg_col _) (reg_col _) _) =>
( apply tac_struct_reg_mapsto_reg_col; vm_compute; eexists _; exact: eq_refl) : typeclass_instances.

Lemma tac_instr_pre_eq `{!Arch} `{islaG Σ} `{threadG} l1 l2 a1 a2 P1 P2:
  a1 = a2 →
  FindHypEqual FICInstrSemantic (instr_pre' l1 a1 P1) (instr_pre' l2 a2 P2) (instr_pre' l2 a1 P2).
Proof. by move => ->. Qed.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr_pre' _ _ _) (instr_pre' _ _ _) _) =>
  ( apply tac_instr_pre_eq; bv_solve) : typeclass_instances.

Lemma tac_instr_eq `{islaG Σ} a1 a2 ins1 ins2:
  a1 = a2 →
  FindHypEqual FICInstrSemantic (instr a1 ins1) (instr a2 ins2) (instr a1 ins2).
Proof. by move => ->. Qed.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr _ _) (instr _ _) _) =>
  ( apply tac_instr_eq; bv_solve) : typeclass_instances.

(* TODO: upstream? *)
Global Opaque FindHypEqual.

(* TODO: upstream? *)
Lemma tac_entails_to_simplify_hyp {Σ} (P Q : iProp Σ):
  (P ⊢ Q)%I → ∀ G, (Q -∗ G) ⊢ simplify_hyp P G.
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
      li_let_bind Φ (fun H => constr:(envs_entails Δ (wp_exp e H)))
    | wp_a_exp ?e ?Φ =>
      li_let_bind Φ (fun H => constr:(envs_entails Δ (wp_a_exp e H)))
    | WPasm (?e:t:?es) =>
      let H := fresh "TRACE" in
      assert_fails (is_var es);
      pose H := (TRACE_LET es);
      change_no_check (envs_entails Δ (WPasm (e:t:H)))
    | (?r ↦ᵣ: ?P)%I =>
      li_let_bind P (fun H => constr:(envs_entails Δ (r ↦ᵣ: H)))
    | (?r # ?f ↦ᵣ: ?P)%I =>
      li_let_bind P (fun H => constr:(envs_entails Δ (r # f ↦ᵣ: H)))
    end
  end
.

Ltac liAAsm :=
  lazymatch goal with
  | |- envs_entails ?Δ (WPasm ?es) =>
    lazymatch es with
    | tnil => notypeclasses refine (tac_fast_apply (li_wp_next_instr) _)
    | tcases _ => notypeclasses refine (tac_fast_apply (li_wp_cases _) _)
    | ?e :t: _ =>
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
      | AbstractPrimop _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_abstract_primop _ _ _ _ _) _)
      end
    | parametric_trace _ _ => iEval (unfold parametric_trace)
    | ?def => first [
                 try unfold TRACE_LET in def; iEval (unfold def); try clear def
               | fail "liAAsm: unknown asm" es
               ]
    end
  | |- envs_entails ?Δ (instr_pre' _ _ _) =>
    notypeclasses refine (tac_fast_apply (li_instr_pre _ _ _) _)
  | |- envs_entails ?Δ (wpreadreg _ [] _) =>
     notypeclasses refine (tac_fast_apply (li_wpreadreg_nil _ _) _)
  | |- envs_entails ?Δ (wpreadreg _ [Field _] _) =>
     notypeclasses refine (tac_fast_apply (li_wpreadreg_field _ _ _) _)
  end.

Ltac liAExp :=
  lazymatch goal with
  (* The following is subsumed by compute_wp_exp. *)
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
  | |- envs_entails _ (?P -∗ _) => li_do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ _ _ ∗ _) => li_do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ _ ∗ _) => li_do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P _ ∗ _) => li_do_unfold P
  | |- envs_entails _ (∃ₗ _, ?P ∗ _) => li_do_unfold P
  | |- envs_entails _ (?P ∗ ?Q) => li_do_unfold P
  end.

Ltac liUnfoldLate :=
  lazymatch goal with
  | |- envs_entails ?Δ (?P) => li_do_unfold P
  end.

Ltac liAOther :=
  lazymatch goal with
  | |- envs_entails ?Δ ?P =>
    lazymatch P with
    | (∃ₗ _, ?r ↦ᵣ: _)%I => notypeclasses refine (tac_fast_apply (reg_mapsto_pred_ex _ _) _)
    | (_ ↦ᵣ: _)%I => notypeclasses refine (tac_fast_apply (reg_mapsto_pred_intro _ _) _)
    end
  end.

Ltac liAStep :=
 liEnsureInvariant;
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

Ltac liARun :=
  time "liARun" repeat liAStep; liShow.
