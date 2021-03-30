From stdpp Require Import coPset.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Export tactics.
From isla Require Export opsem.
Set Default Proof Using "Type".
Import uPred.

Definition instrtblUR : cmra :=
  agreeR (gmapO addr (leibnizO (list trc))).


Class heapG Σ := HeapG {
  heap_instrs_inG :> inG Σ instrtblUR;
  heap_instrs_name : gname;
  heap_regs_inG :> ghost_mapG Σ string valu;
  heap_full_trace : list seq_label;
  heap_spec_trace : list seq_label;
  heap_spec_trace_inG :> ghost_varG Σ (list seq_label);
  heap_spec_trace_name : gname;
}.

Class threadG := ThreadG {
  thread_regs_name : gname;
}.

Definition to_instrtbl : gmap addr (list trc) → instrtblUR :=
  to_agree.

Section definitions.
  Context `{!heapG Σ}.

  Definition instr_table_def (i : gmap addr (list trc)) : iProp Σ :=
    own heap_instrs_name (to_instrtbl i).
  Definition instr_table_aux : seal (@instr_table_def). by eexists. Qed.
  Definition instr_table := unseal instr_table_aux.
  Definition instr_table_eq : @instr_table = @instr_table_def :=
    seal_eq instr_table_aux.

  Definition instr_def (a : addr) (i: option (list trc)) : iProp Σ :=
    ∃ instrs, ⌜instrs !! a = i⌝ ∗ instr_table instrs.
  Definition instr_aux : seal (@instr_def). by eexists. Qed.
  Definition instr := unseal instr_aux.
  Definition instr_eq : @instr = @instr_def :=
    seal_eq instr_aux.

  Definition instr_ctx (intrs : gmap addr (list trc)) : iProp Σ :=
    instr_table intrs.

  Definition reg_mapsto_def (γ : gname) (r : string) (q : frac) (v: valu) : iProp Σ :=
    r ↪[ γ ]{# q} v.
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). by eexists. Qed.
  Definition reg_mapsto := unseal reg_mapsto_aux.
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def :=
    seal_eq reg_mapsto_aux.

  Definition regs_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    ghost_map_auth thread_regs_name 1 regs.

  Definition spec_trace_def (κs: list seq_label) : iProp Σ :=
    ghost_var heap_spec_trace_name (1/2) κs.
  Definition spec_trace_aux : seal (@spec_trace_def). by eexists. Qed.
  Definition spec_trace := unseal spec_trace_aux.
  Definition spec_trace_eq : @spec_trace = @spec_trace_def :=
    seal_eq spec_trace_aux.

  Definition spec_ctx (κs : list seq_label) : iProp Σ :=
    ∃ κscur κsspec_end, ⌜heap_full_trace = κscur ++ κs⌝ ∗
    ⌜heap_spec_trace = κscur ++ κsspec_end⌝ ∗
    ghost_var heap_spec_trace_name (1/2) κsspec_end.

  Definition state_ctx (σ : seq_global_state) (κs : list seq_label) : iProp Σ :=
    spec_ctx κs ∗
    instr_ctx σ.(seq_instrs).

  Definition thread_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    regs_ctx regs.

End definitions.

Notation "r ↦ᵣ{ q } v" := (reg_mapsto thread_regs_name r q v)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_mapsto thread_regs_name r 1 v) (at level 20) : bi_scope.

Section instr.
  Context `{!heapG Σ}.
  Global Instance instr_table_pers i : Persistent (instr_table i).
  Proof. rewrite instr_table_eq. by apply _. Qed.

  Global Instance instr_table_tl i : Timeless (instr_table i).
  Proof. rewrite instr_table_eq. by apply _. Qed.

  Global Instance instr_pers a i : Persistent (instr a i).
  Proof. rewrite instr_eq. by apply _. Qed.

  Global Instance instr_tl a i : Timeless (instr a i).
  Proof. rewrite instr_eq. by apply _. Qed.

  Lemma instr_intro ins a i :
    ins !! a = i →
    instr_table ins -∗ instr a i.
  Proof. rewrite instr_eq. iIntros (?) "?". iExists _. by iFrame. Qed.

  Lemma instr_table_agree i1 i2 :
    instr_table i1 -∗ instr_table i2 -∗ ⌜i1 = i2⌝.
  Proof.
    rewrite instr_table_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
      by fold_leibniz.
  Qed.

  Lemma instr_lookup instrs a i :
    instr_ctx instrs -∗ instr a i -∗ ⌜instrs !! a = i⌝.
  Proof.
    rewrite instr_eq. iIntros "Htbl Hf".
    iDestruct "Hf" as (i2 ?) "Hf".
    by iDestruct (instr_table_agree with "Htbl Hf") as %->.
  Qed.

End instr.

Section reg.
  Context `{!heapG Σ}.

  Global Instance reg_mapsto_tl γ r q v : Timeless (reg_mapsto γ r q v).
  Proof. rewrite reg_mapsto_eq. by apply _. Qed.

  Lemma reg_mapsto_lookup `{!threadG} regs r q v :
    regs_ctx regs -∗ r ↦ᵣ{q} v -∗ ⌜regs !! r = Some v⌝.
  Proof.
    rewrite reg_mapsto_eq.
    iIntros "Hregs Hreg".
    by iDestruct (ghost_map_lookup with "Hregs Hreg") as %?.
  Qed.

  Lemma reg_mapsto_update `{!threadG} regs r v v' :
    regs_ctx regs -∗ r ↦ᵣ v ==∗ regs_ctx (<[r := v']>regs) ∗ r ↦ᵣ v'.
  Proof.
    iIntros "Hregs Hreg".
    iDestruct (reg_mapsto_lookup with "Hregs Hreg") as %?.
    rewrite reg_mapsto_eq.
    by iMod (ghost_map_update with "Hregs Hreg") as "[? $]".
  Qed.
End reg.

Section spec.
  Context `{!heapG Σ}.

  Global Instance spec_trace_tl κs : Timeless (spec_trace κs).
  Proof. rewrite spec_trace_eq. by apply _. Qed.

  Lemma spec_ctx_cons κ κs1 κs2:
    spec_ctx (κ :: κs2) -∗ spec_trace (κ :: κs1) ==∗
    spec_ctx κs2 ∗ spec_trace κs1.
  Proof.
    rewrite spec_trace_eq.
    iDestruct 1 as (?? Hfull Hspec) "Hsc". iIntros "Hs".
    iDestruct (ghost_var_agree with "Hsc Hs") as %?. subst.
    iMod (ghost_var_update_halves with "Hsc Hs") as "[$ ?]".
    iModIntro. iExists _, _. iFrame.
    rewrite cons_middle app_assoc in Hfull.
    rewrite cons_middle app_assoc in Hspec.
    done.
  Qed.

End spec.
