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

  Definition mem_mapsto_word (len : N) (a : bv 64) (w : bv (8*len)) : iProp Σ :=
    let nat_len := N.to_nat len in
    let bytes := bv_to_little nat_len 8 (bv_unsigned w) in
    [∗ list] offset ↦ b ∈ bytes, mem_mapsto heap_mem_name (bv_add a (bv_of_Z 64 (Z.of_nat offset))) 1 b.

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

  (* This isn't true for bv of length 0, so the general form is a mild pain to
  write, so not moving this to bitvector.v for now *)
  Lemma bv_add_Sn z : bv_of_Z 64 (S z) = bv_add [BV{64} 1] (bv_of_Z 64 z).
  Proof.
    unfold bv_add. cbn.
    apply bv_eq.
    repeat rewrite bv_of_Z_unsigned.
    unfold bv_wrap.
    rewrite Z.add_mod_idemp_r.
    + f_equal. lia.
    + done.
  Qed.

  Lemma mem_mapsto_word_lookup_list mem a len w :
    mem_ctx mem -∗ mem_mapsto_word len a w -∗ ⌜read_mem_list mem a (N.to_nat len) = bv_to_little (N.to_nat len) 8 (bv_unsigned w)⌝.
  Proof.
    iIntros "Hmem Ha".
    unfold mem_mapsto_word.
    set (l:= bv_to_little (N.to_nat len) 8 (bv_unsigned w)).
    assert (Hlen : length l = N.to_nat len). {unfold l. apply bv_to_little_len. }
    clearbody l.
    clear w.
    iInduction l as [ | b' bs ] "IH" forall (len a Hlen).
    + cbn in Hlen. rewrite <- Hlen. iPureIntro. reflexivity.
    + cbn in Hlen. rewrite <- Hlen. cbn.
      rewrite bv_add_0.
      iDestruct "Ha" as "[Ha Ha']".
      iDestruct (mem_mapsto_lookup with "Hmem Ha") as %?.
      rewrite H.
      set (a0':=N.of_nat (length bs)).
      set (a1':=bv_add a [BV{64} 1]).
      iAssert (⌜length bs = N.to_nat a0'⌝)%I as "Hlen'".
      { unfold a0'. by rewrite Nat2N.id. }
      iAssert ([∗ list] offset↦b ∈ bs, bv_add a1' (bv_of_Z 64 offset) ↦ₘ b)%I with "[Ha']" as "Hbs".
      { unfold a1'. setoid_rewrite bv_add_Sn. setoid_rewrite bv_add_assoc. iAssumption. }
      iDestruct ("IH" with "Hlen' Hmem Hbs") as "IH'".
      iDestruct "Hlen'" as %Hlen'.
      rewrite Hlen'.
      (* iRewrite doesn't seem to work for me here? *)
      iDestruct "IH'" as %IH'.
      by rewrite IH'.
  Qed.

  Lemma mem_mapsto_word_lookup mem a len w :
    mem_ctx mem -∗ mem_mapsto_word len a w -∗ ⌜read_mem mem a len = w⌝.
  Proof.
    iIntros "Hmem Ha".
    unfold read_mem.
    iDestruct (mem_mapsto_word_lookup_list with "Hmem Ha") as %Ha.
    rewrite Ha.
    rewrite bv_of_to_little.
    rewrite Z.mul_comm.
    assert (H : bv_unsigned w `mod` 2 ^ (Z.of_N 8 * N.to_nat len) = bv_unsigned w).
    + rewrite N_nat_Z. rewrite <- N2Z.inj_mul. apply Zmod_small. apply bv_ok_in_range. exact (bv_is_ok w).
    + rewrite H. by rewrite bv_unsigned_bv_of_Z.
  Qed.

  Lemma bv_to_little_Sn m n w : ∃ x w', bv_to_little (S m) n w = x::(bv_to_little m n w').
  Proof.
    eexists _, _.
    reflexivity.
  Qed.

  Lemma mem_mapsto_word_update_list mem a len w w' :
    mem_ctx mem -∗ mem_mapsto_word len a w ==∗
    mem_ctx (write_mem_list mem a (bv_to_little (N.to_nat len) 8 (bv_unsigned w'))) ∗ mem_mapsto_word len a w'.
  Proof.
    iIntros "Hmem Ha".
    unfold mem_mapsto_word.
    set (l:=bv_to_little (N.to_nat len) 8 (bv_unsigned w')).
    assert (Hlen : length l = N.to_nat len). {unfold l. apply bv_to_little_len. }
    clearbody l.
    clear w'.
    set (w_unsigned := bv_unsigned w).
    clearbody w_unsigned.
    clear w.
    iInduction l as [ | b' bs ] "IH" forall (len mem a w_unsigned Hlen).
    + cbn. iFrame. unfold mem_mapsto_word. rewrite <- Hlen. cbn. iAssumption.
    + cbn.
      cbn in Hlen. rewrite <- Hlen.
      destruct (bv_to_little_Sn (length bs) 8 w_unsigned) as [? [a3' Hlittle]].
      setoid_rewrite Hlittle.
      cbn.
      iDestruct "Ha" as "[Hbyte Hrest]".
      iMod (mem_mapsto_update with "Hmem Hbyte") as "[Hmem Hbyte]".
      rewrite bv_add_0.
      iFrame.
      setoid_rewrite bv_add_Sn.
      setoid_rewrite bv_add_assoc.
      set (a0' := N.of_nat (length bs)).
      set (a1' := <[a:=b']> mem).
      set (a2' := bv_add a [BV{64} 1]).
      assert (Hlen' : length bs = N.to_nat a0').
      { unfold a0'. by rewrite Nat2N.id. }
      rewrite Hlen'.
      (* Shouldn't need this, it's a) trivial and b) exactly Hlen', but I
      couldn't figure out how to rewrite with Hlen' and keep it in the Iris
      context *)
      iAssert (⌜N.to_nat a0' = N.to_nat a0'⌝)%I as "Htriv".
      { by iPureIntro. }
      iDestruct ("IH" with "Htriv Hmem Hrest") as "G".
      iFrame.
  Qed.

  Lemma mem_mapsto_word_update mem a len w w' :
    mem_ctx mem -∗ mem_mapsto_word len a w ==∗
    mem_ctx (write_mem len mem a w') ∗ mem_mapsto_word len a w'.
  Proof.
    iIntros "Hmem Ha".
    unfold write_mem.
    iMod (mem_mapsto_word_update_list with "Hmem Ha") as "[Hmem Ha]".
    by iFrame.
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
