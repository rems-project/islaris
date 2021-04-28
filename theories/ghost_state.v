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

  Definition instr_def (a : Z) (i: option (list trc)) : iProp Σ :=
    ∃ instrs b, ⌜bv_of_Z_checked 64 a = Some b⌝ ∗ ⌜instrs !! b = i⌝ ∗ instr_table instrs.
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

  Definition mem_mapsto_byte_def (γ : gname) (a : addr) (q : dfrac) (v : byte) : iProp Σ :=
    a ↪[ γ ]{q} v.
  Definition mem_mapsto_byte_aux : seal (@mem_mapsto_byte_def). by eexists. Qed.
  Definition mem_mapsto_byte := unseal mem_mapsto_byte_aux.
  Definition mem_mapsto_byte_eq : @mem_mapsto_byte = @mem_mapsto_byte_def :=
    seal_eq mem_mapsto_byte_aux.

  Definition mem_mapsto_def {n} (a : addr) (q : dfrac) (w : bv n) : iProp Σ :=
    ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
    let bytes := bv_to_little len 8 (bv_unsigned w) in
    [∗ list] offset ↦ b ∈ bytes, mem_mapsto_byte heap_mem_name (bv_add_Z a (Z.of_nat offset)) q b.
  Definition mem_mapsto_aux {n} : seal (@mem_mapsto_def n). by eexists. Qed.
  Definition mem_mapsto {n} := unseal (@mem_mapsto_aux n).
  Definition mem_mapsto_eq {n} : @mem_mapsto n = @mem_mapsto_def n :=
    seal_eq mem_mapsto_aux.

  Definition mem_ctx (mem : mem_map) : iProp Σ :=
    ghost_map_auth heap_mem_name 1 mem.

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

Notation "a ↦ₘ{ q } v" := (mem_mapsto a q v)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }  v") : bi_scope.
Notation "a ↦ₘ v" := (mem_mapsto a (DfracOwn 1) v) (at level 20) : bi_scope.

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
    ∀ Hwf,
    ins !! (BV _ a Hwf) = i →
    instr_table ins -∗ instr a i.
  Proof.
    rewrite instr_eq. iIntros (??) "?". iExists _, _. iFrame.
    iPureIntro. split; [|done].
    unfold bv_of_Z_checked. case_option_guard => //.
    f_equal. by apply bv_eq.
  Qed.

  Lemma instr_table_agree i1 i2 :
    instr_table i1 -∗ instr_table i2 -∗ ⌜i1 = i2⌝.
  Proof.
    rewrite instr_table_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
      by fold_leibniz.
  Qed.

  Lemma instr_lookup instrs a i :
    instr_ctx instrs -∗ instr a i -∗ ⌜∃ b, bv_of_Z_checked 64 a = Some b ∧ instrs !! b = i⌝.
  Proof.
    rewrite instr_eq. iIntros "Htbl Hf".
    iDestruct "Hf" as (i2 ? ??) "Hf". iExists _.
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

  Global Instance mem_mapsto_byte_tl γ a q v : Timeless (mem_mapsto_byte γ a q v).
  Proof. rewrite mem_mapsto_byte_eq. by apply _. Qed.

  Global Instance mem_mapsto_tl n a q (v : bv n) : Timeless (a ↦ₘ{q} v).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. by apply _. Qed.

  Lemma mem_mapsto_byte_lookup mem a q v :
    mem_ctx mem -∗ mem_mapsto_byte heap_mem_name a q v -∗ ⌜mem !! a = Some v⌝.
  Proof. rewrite mem_mapsto_byte_eq. apply ghost_map_lookup. Qed.

  Lemma mem_mapsto_byte_lookup_big mem a q bs :
    mem_ctx mem -∗ ([∗ list] i↦v∈ bs, mem_mapsto_byte heap_mem_name (bv_add_Z a i) q v) -∗
          ⌜Forall2 (λ a v, mem !! a = Some v) (bv_seq a (length bs)) bs⌝.
  Proof.
    iIntros "Hmem Hl".
    iInduction bs as [|b bs] "IH" forall (a); simpl. { iPureIntro. constructor. }
    iDestruct "Hl" as "[Ha Hl]". rewrite bv_add_Z_0.
    iDestruct (mem_mapsto_byte_lookup with "Hmem Ha") as %Ha.
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite bv_add_Z_succ.
    iDestruct ("IH" with "Hmem Hl") as %?.
    iPureIntro. rewrite bv_seq_succ; [|lia]. by constructor.
  Qed.

  Lemma mem_mapsto_byte_update mem a v v' :
    mem_ctx mem -∗ mem_mapsto_byte heap_mem_name a (DfracOwn 1) v ==∗
      mem_ctx (<[a := v']> mem) ∗ mem_mapsto_byte heap_mem_name a (DfracOwn 1) v'.
  Proof. rewrite mem_mapsto_byte_eq. apply ghost_map_update. Qed.

  Lemma mem_mapsto_byte_update_big mem a bs bs' :
    length bs = length bs' →
    mem_ctx mem -∗
    ([∗ list] i↦v∈ bs, mem_mapsto_byte heap_mem_name (bv_add_Z a i) (DfracOwn 1) v) ==∗
    mem_ctx (write_mem_list mem a bs') ∗
    ([∗ list] i↦v∈ bs', mem_mapsto_byte heap_mem_name (bv_add_Z a i) (DfracOwn 1) v).
  Proof.
    iIntros (Hlen) "Hmem Hbs".
    iInduction bs as [|b bs] "IH" forall (a mem bs' Hlen); destruct bs' => //; csimpl in *. { by iFrame. }
    iDestruct "Hbs" as "[Ha Hbs]". rewrite bv_add_Z_0.
    iMod (mem_mapsto_byte_update with "Hmem Ha") as "[Hmem $]".
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite bv_add_Z_succ.
    iApply ("IH" with "[] Hmem Hbs"). iPureIntro. lia.
  Qed.

  Lemma mem_mapsto_lookup_list n mem a (w : bv n) q:
    mem_ctx mem -∗ a ↦ₘ{q} w -∗
    ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
        ⌜read_mem_list mem a (N.of_nat len) = Some (bv_to_little len 8 (bv_unsigned w))⌝.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen) "Hlist". subst.
    iExists _. iSplit; [done|].
    iDestruct (mem_mapsto_byte_lookup_big with "Hmem Hlist") as %Hall.
    iPureIntro. apply mapM_Some. rewrite bv_to_little_length in Hall.
    by have ->: (Z.of_N (N.of_nat len) = len) by lia.
  Qed.

  Lemma mem_mapsto_lookup n mem a q (w : bv n) :
    mem_ctx mem -∗ a ↦ₘ{q} w -∗
      ⌜∃ len, n = (8 * len)%N ∧ read_mem mem a len = Some (BVN _ w)⌝.
  Proof.
    iIntros "Hmem Ha". rewrite /read_mem.
    iDestruct (mem_mapsto_lookup_list with "Hmem Ha") as %[len [-> Hl]].
    iPureIntro. eexists _. split; [done|]. rewrite Hl /=. f_equal. apply bvn_eq.
    split; [ done|]. rewrite bv_of_to_little_bv //. lia.
  Qed.

  Lemma mem_mapsto_update_list n mem a (w w' : bv n) :
    mem_ctx mem -∗ a ↦ₘ w ==∗
     ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
      mem_ctx (write_mem_list mem a (bv_to_little len 8 (bv_unsigned w'))) ∗ a ↦ₘ w'.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen) "Hlist". subst.
    iExists _. iSplitR; [done|].
    iMod (mem_mapsto_byte_update_big with "Hmem Hlist") as "[$ H]".
    { by rewrite !bv_to_little_length. }
    iExists _. by iFrame.
  Qed.

  Lemma mem_mapsto_update n mem a (w w' : bv n) :
    mem_ctx mem -∗ a ↦ₘ w ==∗
    ∃ len, ⌜n = (8 * len)%N⌝ ∗ mem_ctx (write_mem len mem a (bv_unsigned w')) ∗ a ↦ₘ w'.
  Proof.
    iIntros "Hmem Ha". unfold write_mem.
    iMod (mem_mapsto_update_list with "Hmem Ha") as (len Hlen) "[Hmem Ha]".
    iExists _. iSplitR; [done|]. iFrame.
    by rewrite Nat2N.id.
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
