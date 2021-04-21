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
  heap_mem_inG :> ghost_mapG Σ addr byte;
  heap_mem_name : gname;
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

  Definition mem_mapsto_def (γ : gname) (a : addr) (q : frac) (v : byte) : iProp Σ :=
    a ↪[ γ ]{# q} v.
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). by eexists. Qed.
  Definition mem_mapsto := unseal mem_mapsto_aux.
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def :=
    seal_eq mem_mapsto_aux.

  Definition mem_ctx (mem : mem_map) : iProp Σ :=
    ghost_map_auth heap_mem_name 1 mem.

  Fixpoint mem_mapsto_word (a : bv) (len : nat) (w : bv) : iProp Σ :=
    match len with
    | 0%nat => ⌜w.(bv_len) = 0 ∧ w.(bv_val) = 0⌝
    | S n =>
      let next := bv_add a [BV{64} 1] in
      let byte := (bv_extract 7 0 w) in
      let rest := bv_extract (w.(bv_len) - 1) 8 w in
      mem_mapsto heap_mem_name a.(bv_val) 1 byte ∗
      mem_mapsto_word next n rest
    end.

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
    instr_ctx σ.(seq_instrs) ∗
    mem_ctx σ.(seq_mem).

  Definition thread_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    regs_ctx regs.

End definitions.

Notation "r ↦ᵣ{ q } v" := (reg_mapsto thread_regs_name r q v)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_mapsto thread_regs_name r 1 v) (at level 20) : bi_scope.


Notation "a ↦ₘ{ q } v" := (mem_mapsto heap_mem_name a q v)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }  v") : bi_scope.
Notation "a ↦ₘ v" := (mem_mapsto heap_mem_name a 1 v) (at level 20) : bi_scope.

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

Section mem.
  Context `{!heapG Σ}.

  Global Instance mem_mapsto_tl γ a q v : Timeless (mem_mapsto γ a q v).
  Proof. rewrite mem_mapsto_eq. by apply _. Qed.

  Lemma mem_mapsto_lookup mem a q v :
    mem_ctx mem -∗ a ↦ₘ{q} v -∗ ⌜mem !! a = Some v⌝.
  Proof.
    rewrite mem_mapsto_eq.
    iIntros "Hmem Ha".
    by iDestruct (ghost_map_lookup with "Hmem Ha") as %?.    
  Qed.

  Lemma mem_mapsto_update mem a v v' :
    mem_ctx mem -∗ a ↦ₘ v ==∗ mem_ctx (<[a := v']> mem) ∗ a ↦ₘ v'.
  Proof.
    iIntros "Hmem Ha".
    iDestruct (mem_mapsto_lookup with "Hmem Ha") as %?.
    rewrite mem_mapsto_eq.
    by iMod (ghost_map_update with "Hmem Ha") as "[? $]".
  Qed.

  Lemma mem_mapsto_word_lookup mem a len w :
    mem_ctx mem -∗ mem_mapsto_word a len w -∗ ⌜read_mem mem a len = w⌝.
  Proof.
    iIntros "Hmem Ha".
    iInduction len as [ | n ] "IH" forall (w a).
    + unfold read_mem.
      unfold mem_mapsto_word.
      iDestruct "Ha" as %[Ha1 Ha2].
      iPureIntro.
      destruct w.
      cbn in Ha1.
      cbn in Ha2.
      rewrite Ha1 Ha2.
      done.
    + cbn.
      iDestruct "Ha" as "[Hbyte Hrest]".
      iDestruct (mem_mapsto_lookup with "Hmem Hbyte") as %?.
      rewrite H.
      set (next:=(bv_add a [BV{64} 1])).
      iDestruct ("IH" with "Hmem Hrest") as "H".
      iDestruct "H" as %G.
      rewrite G.
      iPureIntro.
      apply (bv_concat_split 7 w).
  Qed.

  Definition rest (w : bv) := bv_extract (bv_len w - 1) 8 w.

  Lemma len_rest (w : bv) : bv_len (rest w) = bv_len w - 8.
  Proof.
    cbn.
    lia.
  Qed.

  Lemma mem_mapsto_word_update mem a len w w' :
    ⌜w.(bv_len) = w'.(bv_len)⌝ -∗ mem_ctx mem -∗ mem_mapsto_word a len w ==∗
    mem_ctx (write_mem mem a w' len) ∗ mem_mapsto_word a len w'.
  Proof.
    iIntros "Hlen Hmem Ha".
    iInduction len as [ | n ] "IH" forall (w w' a mem).
    + cbn.
      iModIntro. iFrame.
      iDestruct "Hlen" as %Hlen.
      iDestruct "Ha" as %[Hwlen Hwval].
      iPureIntro; split. { rewrite <- Hlen. assumption. }
      apply bv_zero_len. rewrite <- Hlen. assumption.
    + cbn.
      iDestruct "Ha" as "[Hbyte Hrest]".
      fold (rest w) (rest w').
      iDestruct "Hlen" as %Hlen.
      iAssert ⌜bv_len (rest w) = bv_len (rest w')⌝%I as "Hlen'".
      {
        repeat rewrite len_rest.
        by rewrite Hlen.
      }
      iMod (mem_mapsto_update with "Hmem Hbyte") as "[Hmem Hbyte]".
      iMod ("IH" with "Hlen' Hmem Hrest") as "[Hmem Hrest]".
      iModIntro.
      iFrame.
  Qed.
      
End mem.

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
