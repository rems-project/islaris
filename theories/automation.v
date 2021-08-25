From iris.proofmode Require Import coq_tactics reduction.
From refinedc.lithium Require Export lithium tactics.
From isla Require Export lifting bitvector_auto.
Set Default Proof Using "Type".

(** * Simplification and normalization hints *)
Global Instance simpl_val_bits_bv_to_bvn n (b1 b2 : bv n) :
  SimplBoth (Val_Bits b1 = Val_Bits b2) (b1 = b2).
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

Lemma ite_bits n b (n1 n2 : bv n) :
  ite b (Val_Bits n1) (Val_Bits n2) = Val_Bits (ite b n1 n2).
Proof. by destruct b. Qed.
Hint Rewrite ite_bits : lithium_rewrite.

Hint Rewrite Z_to_bv_checked_bv_unsigned : lithium_rewrite.

Global Instance simpl_SWriteMem a1 a2 v1 v2:
  SimplBoth (SWriteMem a1 v1 = SWriteMem a2 v2) (a1 = a2 ∧ v1 = v2).
Proof. split; naive_solver. Qed.

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Ltac normalize_tac ::= normalize_autorewrite.

(* injection on bitvectors sometimes creates weird matches, so we disable it. *)
Ltac li_impl_check_injection_tac ::=
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
Definition FindInstrKind {Σ} `{!islaG Σ} `{!threadG} (a : Z) (l : bool) := {|
  fic_A := @instr_kind Σ;
  fic_Prop ik :=
    match ik with
    | IKInstr ins => instr a ins
    | IKPre l' P => instr_pre' l' a P
    end
|}.
Typeclasses Opaque FindInstrKind.

(* If we ever need to support more than one reg_col, we can use
a solver for finding the collection with the right r. *)
Inductive reg_mapsto_kind : Type :=
| RKMapsTo (v : valu) | RKCol (regs : list (reg_col_entry * valu)).
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

Inductive mem_mapsto_kind (n : N) : Type :=
| MKMapsTo (v : bv n) | MKArray (a : addr) (l : list (bv n)) | MKMMIO (a : addr) (l : Z).
Definition FindMemMapsTo {Σ} `{!islaG Σ} `{!threadG} (a : addr) (n : N) := {|
  fic_A := mem_mapsto_kind n;
  fic_Prop mk :=
  match mk with
  | MKMapsTo _ v => (a ↦ₘ v)%I
  | MKArray _ a' l => (a' ↦ₘ∗ l)%I
  | MKMMIO _ a' l => mmio_range a' l
  end
|}.

Section instances.
  Context `{!islaG Σ} `{!threadG}.

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
    rt_fic := FindMemMapsTo a n;
  |}.

  Lemma find_in_context_mem_mapsto_id a n T:
    (∃ v : bv n, a ↦ₘ v ∗ T (MKMapsTo n v)) -∗
    find_in_context (FindMemMapsTo a n) T.
  Proof. iDestruct 1 as (v) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_mapsto_id_inst a n :
    FindInContext (FindMemMapsTo a n) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_mem_mapsto_id a n T).

  Inductive FICMemMapstoSemantic (a : addr) (n : N) : Set :=.
  Global Instance find_in_context_mem_mapsto_semantic_inst a n :
    FindInContext (FindMemMapsTo a n) (FICMemMapstoSemantic a n) | 10 :=
    λ T, i2p (find_in_context_mem_mapsto_id a n T).

  Lemma tac_mem_mapsto_eq `{!islaG Σ} l1 l' n' n (v1 v2 : bv n) l2:
    l1 = l2 →
    FindHypEqual (FICMemMapstoSemantic l' n') (l1 ↦ₘ v1) (l2 ↦ₘ v2) (l1 ↦ₘ v2).
  Proof. by move => ->. Qed.

  Lemma find_in_context_mem_mapsto_array a n T:
    (∃ a' l, a' ↦ₘ∗ l ∗ T (MKArray n a' l)) -∗
    find_in_context (FindMemMapsTo a n) T.
  Proof. iDestruct 1 as (a' l) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_mapsto_array_inst a n :
    FindInContext (FindMemMapsTo a n) (FICMemMapstoSemantic a n) | 20 :=
    λ T, i2p (find_in_context_mem_mapsto_array a n T).

  Lemma tac_mem_mapsto_array_eq a n a1 a2 (l1 l2 : list (bv n)):
    bv_unsigned a1 ≤ bv_unsigned a ≤ bv_unsigned a1 + length l1 * Z.of_N n `div` 8 →
    FindHypEqual (FICMemMapstoSemantic a n) (a1 ↦ₘ∗ l1) (a2 ↦ₘ∗ l2) (a2 ↦ₘ∗ l2).
  Proof. done. Qed.

  Lemma find_in_context_mem_mapsto_mmio a n T:
    (∃ a' l, mmio_range a' l ∗ T (MKMMIO n a' l)) -∗
    find_in_context (FindMemMapsTo a n) T.
  Proof. iDestruct 1 as (a' l) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_mem_mapsto_mmio_semantic_inst a n :
  FindInContext (FindMemMapsTo a n) (FICMemMapstoSemantic a n) | 30 :=
  λ T, i2p (find_in_context_mem_mapsto_mmio a n T).

  Lemma tac_mem_mapsto_mmio a n a1 a2 l1 l2:
    bv_unsigned a1 ≤ bv_unsigned a ≤ bv_unsigned a1 + l1 →
    FindHypEqual (FICMemMapstoSemantic a n) (mmio_range a1 l1) (mmio_range a2 l2) (mmio_range a2 l2).
  Proof. done. Qed.

  Global Instance reg_related r v : RelatedTo (r ↦ᵣ v) := {|
    rt_fic := FindDirect (λ v, r ↦ᵣ v)%I;
  |}.

  Global Instance struct_reg_related r f v : RelatedTo (r # f ↦ᵣ v) := {|
    rt_fic := FindDirect (λ v, r # f ↦ᵣ v)%I;
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
  Global Instance find_in_context_reg_mapsto_col_inst r :
    FindInContext (FindRegMapsTo r) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_reg_mapsto_col r T).

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
  Global Instance find_in_context_struct_reg_mapsto_col_inst r f:
    FindInContext (FindStructRegMapsTo r f) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_struct_reg_mapsto_col r f T).

  Global Instance instr_related a i : RelatedTo (instr a i) := {|
    rt_fic := FindDirect (λ i, instr a i)%I;
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

  Lemma subsume_instr a i1 i2 G:
    ⌜i1 = i2⌝ ∗ G -∗
    subsume (instr a i1) (instr a i2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_instr_inst a i1 i2 :
    Subsume (instr a i1) (instr a i2) :=
    λ G, i2p (subsume_instr a i1 i2 G).

  Lemma subsume_spec_trace κs1 κs2 G:
    ⌜κs1 = κs2⌝ ∗ G -∗
    subsume (spec_trace κs1) (spec_trace κs2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_spec_trace_inst κs1 κs2 :
    Subsume (spec_trace κs1) (spec_trace κs2) :=
    λ G, i2p (subsume_spec_trace κs1 κs2 G).

  Lemma subsume_mem `{!islaG Σ} a n (v1 v2 : bv n) G:
    ⌜v1 = v2⌝ ∗ G -∗
    subsume (a ↦ₘ v1) (a ↦ₘ v2) G.
  Proof. iDestruct 1 as (->) "$". iIntros "$". Qed.
  Global Instance subsume_mem_inst  `{!islaG Σ} a n (v1 v2 : bv n) :
    Subsume (a ↦ₘ v1) (a ↦ₘ v2) :=
    λ G, i2p (subsume_mem a n v1 v2 G).

  Lemma li_wp_next_instr:
    (∃ (nPC : addr) bPC_changed,
        "_PC" ↦ᵣ Val_Bits nPC ∗ "__PC_changed" ↦ᵣ Val_Bool bPC_changed ∗
     ∃ a newPC,
       ⌜a = (if (bPC_changed : bool) then (via_vm_compute bv_unsigned nPC) else (via_vm_compute (Z.add (bv_unsigned nPC)) 4)%Z)⌝ ∗
       ⌜Z_to_bv_checked 64 a = Some newPC⌝ ∗
     find_in_context (FindInstrKind a true) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, "_PC" ↦ᵣ Val_Bits newPC -∗ "__PC_changed" ↦ᵣ Val_Bool false -∗ WPasm t
     | IKInstr (None) =>
       ∃ κs, spec_trace κs ∗ ⌜hd_error κs = Some (SInstrTrap newPC)⌝ ∗ True
     | IKPre l P => P
     end
    )) -∗
    WPasm [].
  Proof.
    iDestruct 1 as (??) "(HPC&Hchanged&Hwp)".
    iDestruct "Hwp" as (???? ins) "[Hi Hwp]". subst.
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iApply (wp_next_instr with "[HPC Hchanged] Hi [Hl]") => //.
      + iExists _, _, _. rewrite ->!via_vm_compute_eq in *. by iFrame.
      + iIntros "!>" (i Hi) "? ?".
        iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
        iApply ("Hwp" with "[$] [$]").
    - iDestruct "Hwp" as (?) "(?&%&?)".
      iApply (wp_next_instr_extern with "[HPC Hchanged] [$] [$]") => //.
      iExists _, _, _. rewrite ->!via_vm_compute_eq in *. by iFrame.
    - iApply (wp_next_instr_pre with "[$] [HPC Hchanged] [$]").
      iExists _, _, _. rewrite ->!via_vm_compute_eq in *. by iFrame.
  Qed.

  Lemma li_instr_pre l a P:
    (∃ newPC, ⌜Z_to_bv_checked 64 a = Some newPC⌝ ∗
     find_in_context (FindInstrKind a l) (λ ik,
     match ik with
     | IKInstr (Some ts) =>
       ⌜ts ≠ []⌝ ∗ [∧ list] t∈ts, P -∗ "_PC" ↦ᵣ Val_Bits newPC -∗ "__PC_changed" ↦ᵣ Val_Bool false -∗ WPasm t
     | IKInstr None =>
       P -∗ ∃ κs, spec_trace κs ∗ ⌜hd_error κs = Some (SInstrTrap newPC)⌝ ∗ True
     | IKPre l' Q => ⌜implb l' l⌝ ∗ (P -∗ Q)
     end
    )) -∗
    instr_pre' l a P.
  Proof.
    iDestruct 1 as (?? ins) "[Hinstr Hwp]".
    destruct ins as [[?|]|?] => /=.
    - iDestruct "Hwp" as (?) "Hl".
      iApply (instr_pre_intro_Some with "[$]"); [done..|].
      iIntros (i Hi) "???".
      iDestruct (big_andL_elem_of with "Hl") as "Hwp"; [done|].
      iApply ("Hwp" with "[$] [$] [$]").
    - iApply (instr_pre_intro_None with "[$]"); [done..|].
      iIntros "HP".
      iDestruct ("Hwp" with "HP") as (?) "[? [% _]]".
      iExists _. by iFrame.
    - iDestruct "Hwp" as (?) "Hwand".
      by iApply (instr_pre_wand with "Hinstr").
  Qed.

  Lemma li_wp_read_reg r v ann es :
    (find_in_context (FindRegMapsTo r) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜v = v'⌝ -∗ r ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => ⌜is_Some (via_vm_compute (list_find_idx (λ x, x.1 = RegColDirect r)) regs)⌝ ∗
                      (reg_col regs -∗ WPasm es)
      end)) -∗
    WPasm (ReadReg r [] v ann :: es).
  Proof.
    iDestruct 1 as (rk) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_read_reg with "Hr").
    - rewrite via_vm_compute_eq.
      iDestruct "Hwp" as ([? [[??][?[??]]]%list_find_idx_Some]) "Hwp"; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[Hr Hregs]"; [done|] => /=.
      iApply (wp_read_reg with "Hr"). iIntros "_ Hr". iApply "Hwp". by iApply "Hregs".
  Qed.

  Lemma li_wp_read_reg_struct r f v ann es :
    (∃ vread, ⌜read_accessor [Field f] v = Some vread⌝ ∗
     (find_in_context (FindStructRegMapsTo r f) (λ rk,
      match rk with
      | RKMapsTo v' => (⌜vread = v'⌝ -∗ r # f ↦ᵣ v' -∗ WPasm es)
      | RKCol regs => ⌜is_Some (via_vm_compute (list_find_idx (λ x, x.1 = RegColStruct r f)) regs)⌝ ∗
                      (reg_col regs -∗ WPasm es)
      end))) -∗
    WPasm (ReadReg r [Field f] v ann :: es).
  Proof.
    iDestruct 1 as (???) "[Hr Hwp]" => /=. case_match; simplify_eq.
    - by iApply (wp_read_reg_struct with "Hr").
    - rewrite via_vm_compute_eq.
      iDestruct "Hwp" as ([? [[??][?[??]]]%list_find_idx_Some]) "Hwp"; simplify_eq/=.
      iDestruct (big_sepL_lookup_acc with "Hr") as "[Hr Hregs]"; [done|] => /=.
      iApply (wp_read_reg_struct with "Hr"); [done|]. iIntros "_ Hr". iApply "Hwp". by iApply "Hregs".
  Qed.

  Lemma li_wp_write_reg r v ann es:
    (∃ v', r ↦ᵣ v' ∗ (r ↦ᵣ v -∗ WPasm es)) -∗
    WPasm (WriteReg r [] v ann :: es).
  Proof. iDestruct 1 as (?) "[Hr Hwp]". by iApply (wp_write_reg with "Hr"). Qed.

  Lemma li_wp_write_reg_struct r f v ann es:
    (∃ v' vnew, r # f ↦ᵣ v' ∗
     ⌜read_accessor [Field f] v = Some vnew⌝ ∗
     (r # f ↦ᵣ vnew -∗ WPasm es)) -∗
    WPasm (WriteReg r [Field f] v ann :: es).
  Proof. iDestruct 1 as (??) "[Hr [% Hwp]]". by iApply (wp_write_reg_struct with "Hr"). Qed.

  Lemma li_wp_branch_address v ann es:
    WPasm es -∗
    WPasm (BranchAddress v ann :: es).
  Proof. apply: wp_branch_address. Qed.

  Lemma li_wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm ((subst_event v (Val_Bits n)) <$> es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof. apply: wp_declare_const_bv. Qed.

  Lemma li_wp_declare_const_bool v es ann:
    (∀ b : bool, WPasm ((subst_event v (Val_Bool b)) <$> es)) -∗
    WPasm (Smt (DeclareConst v Ty_Bool) ann :: es).
  Proof. apply: wp_declare_const_bool. Qed.

  Lemma li_wp_define_const n es ann e:
    WPexp e {{ v, let_bind_hint v (λ v, WPasm ((subst_event n v) <$> es)) }} -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof.
    iIntros "Hexp". iApply wp_define_const. unfold let_bind_hint.
    iApply (wpe_wand with "Hexp"). iIntros (?) "$".
  Qed.

  Lemma li_wp_assert es ann e:
    WPexp e {{ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es) }} -∗
    WPasm (Smt (Assert e) ann :: es).
  Proof. apply: wp_assert. Qed.

  Lemma li_wp_write_mem len n success kind a (vnew : bv n) tag ann es:
    (⌜n = (8*len)%N⌝ ∗
    ⌜len ≠ 0%N⌝ ∗
    find_in_context (FindMemMapsTo a n) (λ mk,
      match mk with
      | MKMapsTo _ vold => (a ↦ₘ vnew -∗ WPasm es)
      | MKArray _ a' l => False
      | MKMMIO _ a' l =>
        ⌜bv_unsigned a' ≤ bv_unsigned a⌝ ∗ ⌜bv_unsigned a + Z.of_N len ≤ bv_unsigned a' + l⌝ ∗
        ∃ κs, spec_trace κs ∗ ⌜head κs = Some (SWriteMem a vnew)⌝ ∗
        (spec_trace (tail κs) -∗ WPasm es)
      end
    )) -∗
    WPasm (WriteMem (Val_Bool success) kind (Val_Bits (BVN 64 a)) (Val_Bits (BVN n vnew)) len tag ann :: es).
  Proof.
    iDestruct 1 as (?? mk) "[HP Hcont]" => /=. case_match.
    - iApply (wp_write_mem with "HP Hcont"); [done | lia].
    - done.
    - iDestruct "Hcont" as (?? κs) "[Hκs [% Hcont]]". destruct κs => //; simplify_eq/=.
      iApply (wp_write_mmio with "[HP] Hκs"); [done | lia| | ].
      { iApply (mmio_range_shorten with "HP"); lia. }
      done.
  Qed.

  Lemma li_wp_read_mem len n kind a vread tag ann es:
    (⌜n = (8 * len)%N⌝ ∗
    ⌜len ≠ 0%N⌝ ∗
    find_in_context (FindMemMapsTo a n) (λ mk,
      match mk with
      | MKMapsTo _ vmem => (⌜vread = vmem⌝ -∗ a ↦ₘ vmem -∗ WPasm es)
      | MKArray _ a' l => ∃ i : nat, ⌜a = bv_add_Z a' (i * Z.of_N len)⌝ ∗ ⌜i < length l⌝%nat ∗
         (∀ vmem, ⌜l !! i = Some vmem⌝ -∗ ⌜vread = vmem⌝ -∗ a' ↦ₘ∗ l -∗ WPasm es)
      | MKMMIO _ _ _ => False
      end)) -∗
    WPasm (ReadMem (Val_Bits (BVN n vread)) kind (Val_Bits (BVN 64 a)) len tag ann :: es).
  Proof.
    iDestruct 1 as (?? mk) "[Hmem Hcont]" => /=. case_match.
    - iApply (wp_read_mem with "Hmem Hcont"); [done|lia].
    - iDestruct "Hcont" as (i?[??]%lookup_lt_is_Some_2) "Hcont".
      iApply (wp_read_mem_array with "Hmem [Hcont]"); [done|lia|done|done|].
      iIntros (?) "Hl". by iApply "Hcont".
    - done.
  Qed.

  Lemma li_wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. apply: wpe_val. Qed.

  Lemma li_wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPexp (Manyop op es ann) {{ Φ }}.
  Proof. apply: wpe_manyop. Qed.

  Lemma li_wpe_unop op e Φ ann:
    WPexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPexp (Unop op e ann) {{ Φ }}.
  Proof. apply: wpe_unop. Qed.

  Lemma li_wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof. apply: wpe_binop. Qed.

  Lemma li_wpe_ite e1 e2 e3 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, WPexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPexp (Ite e1 e2 e3 ann) {{ Φ }}.
  Proof. apply: wpe_ite. Qed.
End instances.

#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _ _) (_ ↦ₘ _) (_ ↦ₘ _) _) =>
  ( apply tac_mem_mapsto_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _ _) (_ ↦ₘ∗ _) (_ ↦ₘ∗ _) _) =>
  ( apply tac_mem_mapsto_array_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual (FICMemMapstoSemantic _ _) (mmio_range _ _) (mmio_range _ _) _) =>
  ( apply tac_mem_mapsto_mmio; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr_pre' _ _ _) (instr_pre' _ _ _) _) =>
  ( apply tac_instr_pre_eq; bv_solve) : typeclass_instances.
#[ global ] Hint Extern 10 (FindHypEqual FICInstrSemantic (instr _ _) (instr _ _) _) =>
  ( apply tac_instr_eq; bv_solve) : typeclass_instances.

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

Ltac liAAsm :=
  lazymatch goal with
  | |- envs_entails ?Δ (WPasm ?es) =>
    lazymatch es with
    | [] => notypeclasses refine (tac_fast_apply (li_wp_next_instr) _)
    | ?e :: _ =>
      lazymatch e with
      | ReadReg _ [] _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_reg _ _ _ _) _)
      | ReadReg _ [Field _] _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_reg_struct _ _ _ _ _) _)
      | WriteReg _ [] _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_reg _ _ _ _) _)
      | WriteReg _ [Field _] _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_reg_struct _ _ _ _ _) _)
      | BranchAddress _ _ => notypeclasses refine (tac_fast_apply (li_wp_branch_address _ _ _) _)
      | ReadMem _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_read_mem _ _ _ _ _ _ _ _) _)
      | WriteMem _ _ _ _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wp_write_mem _ _ _ _ _ _ _ _ _) _)
      | Smt (DeclareConst _ (Ty_BitVec _)) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bv _ _ _ _) _)
      | Smt (DeclareConst _ Ty_Bool) _ => notypeclasses refine (tac_fast_apply (li_wp_declare_const_bool _ _ _) _)
      | Smt (DefineConst _ _) _ => notypeclasses refine (tac_fast_apply (li_wp_define_const _ _ _ _) _)
      | Smt (Assert _) _ => notypeclasses refine (tac_fast_apply (li_wp_assert _ _ _) _)
      end
    | ?def => first [
                 iEval (unfold def)
               | fail "liAAsm: unknown asm" es
               ]
    end
  | |- envs_entails ?Δ (instr_pre' _ _ _) =>
    notypeclasses refine (tac_fast_apply (li_instr_pre _ _ _) _)
  end.

Ltac liAExp :=
  lazymatch goal with
  | |- envs_entails ?Δ (wp_exp ?e _) =>
    lazymatch e with
    | Val _ _ => notypeclasses refine (tac_fast_apply (li_wpe_val _ _ _) _)
    | Manyop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_manyop _ _ _ _) _)
    | Unop _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_unop _ _ _ _) _)
    | Binop _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_binop _ _ _ _ _) _)
    | Ite _ _ _ _ => notypeclasses refine (tac_fast_apply (li_wpe_ite _ _ _ _ _) _)
    | _ => fail "liAExp: unknown exp" e
    end
  end.


Ltac liAStep :=
 liEnforceInvariantAndUnfoldInstantiatedEvars;
 first [
    liAAsm
  | liAExp
  | liStep
  | liLetBindHint
]; liSimpl.
