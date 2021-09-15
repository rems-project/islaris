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

Definition backed_memUR : cmra :=
  agreeR (leibnizO (gset addr)).


Class heapG Σ := HeapG {
  heap_instrs_inG :> inG Σ instrtblUR;
  heap_instrs_name : gname;
  heap_regs_inG :> ghost_mapG Σ string valu;
  heap_struct_regs_inG :> ghost_mapG Σ (string * string) valu;
  heap_mem_inG :> ghost_mapG Σ addr byte;
  heap_mem_name : gname;
  heap_backed_mem_inG :> inG Σ backed_memUR;
  heap_backed_mem_name : gname;
  heap_full_trace : list seq_label;
  heap_spec_trace : list seq_label;
  heap_spec_trace_inG :> ghost_varG Σ (list seq_label);
  heap_spec_trace_name : gname;
}.

Class threadG := ThreadG {
  thread_regs_name : gname;
  thread_struct_regs_name : gname;
}.

Definition to_instrtbl : gmap addr (list trc) → instrtblUR :=
  to_agree.

Definition to_backed_mem : gset addr → backed_memUR :=
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
    ∃ instrs b, ⌜Z_to_bv_checked 64 a = Some b⌝ ∗ ⌜instrs !! b = i⌝ ∗ instr_table instrs.
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

  Definition struct_reg_mapsto_def (γ : gname) (r f : string) (q : frac) (v: valu) : iProp Σ :=
    (r, f) ↪[ γ ]{# q} v.
  Definition struct_reg_mapsto_aux : seal (@struct_reg_mapsto_def). by eexists. Qed.
  Definition struct_reg_mapsto := unseal struct_reg_mapsto_aux.
  Definition struct_reg_mapsto_eq : @struct_reg_mapsto = @struct_reg_mapsto_def :=
    seal_eq struct_reg_mapsto_aux.

  Inductive reg_col_entry :=
  | RegColDirect (r : string) | RegColStruct (r f : string).
  Global Instance reg_col_entry_eq_decision : EqDecision reg_col_entry.
  Proof. solve_decision. Defined.

  Definition reg_col `{!threadG} (regs : list (reg_col_entry * valu)) : iProp Σ :=
    [∗ list] v ∈ regs, match v.1 with
                       | RegColDirect r => reg_mapsto thread_regs_name r 1 v.2
                       | RegColStruct r f => struct_reg_mapsto thread_struct_regs_name r f 1 v.2
                       end.

  Definition regs_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    ∃ rs (srs : gmap (string * string) valu),
      ⌜map_Forall (λ r v, regs !! r = Some v) rs⌝ ∗
      ⌜map_Forall (λ r v, ∃ l i, regs !! r.1 = Some (RegVal_Struct l) ∧
         list_find_idx (λ x, x.1 = r.2) l = Some i ∧ l !! i = Some (r.2, v)) srs⌝ ∗
      ⌜∀ i, is_Some (rs !! i) → (∃ f, is_Some (srs !! (i, f))) → False⌝ ∗
      ghost_map_auth thread_regs_name 1 rs ∗
      ghost_map_auth thread_struct_regs_name 1 srs
  .

  Definition backed_mem_def (m : gset addr) : iProp Σ :=
    own heap_backed_mem_name (to_backed_mem m).
  Definition backed_mem_aux : seal (@backed_mem_def). by eexists. Qed.
  Definition backed_mem := unseal backed_mem_aux.
  Definition backed_mem_eq : @backed_mem = @backed_mem_def :=
    seal_eq backed_mem_aux.

  Definition mmio_range_def (a : addr) (len : Z) : iProp Σ :=
    ∃ bm, ⌜0 ≤ len⌝ ∗ ⌜set_Forall (λ a', ¬ (bv_unsigned a ≤ bv_unsigned a' < bv_unsigned a + len)) bm⌝ ∗
           backed_mem bm.
  Definition mmio_range_aux : seal (@mmio_range_def). by eexists. Qed.
  Definition mmio_range := unseal mmio_range_aux.
  Definition mmio_range_eq : @mmio_range = @mmio_range_def :=
    seal_eq mmio_range_aux.

  Definition mem_mapsto_byte_def (γ : gname) (a : addr) (q : dfrac) (v : byte) : iProp Σ :=
    a ↪[ γ ]{q} v.
  Definition mem_mapsto_byte_aux : seal (@mem_mapsto_byte_def). by eexists. Qed.
  Definition mem_mapsto_byte := unseal mem_mapsto_byte_aux.
  Definition mem_mapsto_byte_eq : @mem_mapsto_byte = @mem_mapsto_byte_def :=
    seal_eq mem_mapsto_byte_aux.

  Definition mem_mapsto_def {n} (a : addr) (q : dfrac) (w : bv n) : iProp Σ :=
    ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
    let bytes := bv_to_little_endian len 8 (bv_unsigned w) in
    [∗ list] offset ↦ b ∈ bytes, mem_mapsto_byte heap_mem_name (bv_add_Z a (Z.of_nat offset)) q b.
  Definition mem_mapsto_aux {n} : seal (@mem_mapsto_def n). by eexists. Qed.
  Definition mem_mapsto {n} := unseal (@mem_mapsto_aux n).
  Definition mem_mapsto_eq {n} : @mem_mapsto n = @mem_mapsto_def n :=
    seal_eq mem_mapsto_aux.

  Definition mem_mapsto_array_def {n} (a : addr) (q : dfrac) (l : list (bv n)) : iProp Σ :=
    ∃ len, ⌜n = (len * 8)%N⌝ ∗
    [∗ list] i↦v∈l, mem_mapsto (bv_add_Z a (i * Z.of_N len)) q v.
  Definition mem_mapsto_array_aux {n} : seal (@mem_mapsto_array_def n). by eexists. Qed.
  Definition mem_mapsto_array {n} := unseal (@mem_mapsto_array_aux n).
  Definition mem_mapsto_array_eq {n} : @mem_mapsto_array n = @mem_mapsto_array_def n :=
    seal_eq mem_mapsto_array_aux.

  Definition mem_ctx (mem : mem_map) : iProp Σ :=
    ghost_map_auth heap_mem_name 1 mem ∗ backed_mem (dom _ mem).

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

Notation "r # f ↦ᵣ{ q } v" := (struct_reg_mapsto thread_struct_regs_name r f q v)
  (at level 20, f at level 10, q at level 50, format "r  #  f  ↦ᵣ{ q }  v") : bi_scope.
Notation "r  #  f  ↦ᵣ v" := (struct_reg_mapsto thread_struct_regs_name r f 1 v)
  (at level 20, f at level 10) : bi_scope.

Notation "a ↦ₘ{ q } v" := (mem_mapsto a q v)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }  v") : bi_scope.
Notation "a ↦ₘ v" := (mem_mapsto a (DfracOwn 1) v) (at level 20) : bi_scope.

Notation "a ↦ₘ{ q }∗ l" := (mem_mapsto_array a q l)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }∗  l") : bi_scope.
Notation "a ↦ₘ∗ l" := (mem_mapsto_array a (DfracOwn 1) l) (at level 20) : bi_scope.

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
    unfold Z_to_bv_checked. case_option_guard => //.
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
    instr_ctx instrs -∗ instr a i -∗ ⌜∃ b, Z_to_bv_checked 64 a = Some b ∧ instrs !! b = i⌝.
  Proof.
    rewrite instr_eq. iIntros "Htbl Hf".
    iDestruct "Hf" as (i2 ? ??) "Hf". iExists _.
    by iDestruct (instr_table_agree with "Htbl Hf") as %->.
  Qed.

End instr.

Section reg.
  Context `{!heapG Σ} `{!threadG}.

  Global Instance reg_mapsto_tl γ r q v : Timeless (reg_mapsto γ r q v).
  Proof. rewrite reg_mapsto_eq. by apply _. Qed.

  Global Instance struct_reg_mapsto_tl γ r f q v : Timeless (struct_reg_mapsto γ r f q v).
  Proof. rewrite struct_reg_mapsto_eq. by apply _. Qed.

  Lemma reg_mapsto_to_struct_reg_mapsto regs r l:
    NoDup l.*1 →
    regs_ctx regs -∗ r ↦ᵣ RegVal_Struct l ==∗ regs_ctx regs ∗ [∗ list] v∈l, r # v.1 ↦ᵣ v.2.
  Proof.
    rewrite reg_mapsto_eq struct_reg_mapsto_eq.
    iIntros (?) "(%rs&%srs&%Hrs&%Hsrs&%Hdisj&Hregs&Hsregs) Hreg".
    iDestruct (ghost_map_lookup with "Hregs Hreg") as %?.
    iMod (ghost_map_delete with "Hregs Hreg") as "Hregs".
    iMod (ghost_map_insert_big (kmap (λ x, (r, x)) (list_to_map l)) with "Hsregs") as "[Hsregs Hl]".
    { apply map_disjoint_spec => -[??]?? /lookup_kmap_Some. naive_solver. }
    iModIntro. iSplitR "Hl".
    - iExists _, _. iFrame. iPureIntro. split_and!.
      + by apply: map_Forall_delete.
      + apply map_Forall_union; [| split; [|done]].
        { apply map_disjoint_spec => -[??]?? /lookup_kmap_Some. naive_solver. }
        move => [??] /=? /lookup_kmap_Some[?[? /elem_of_list_to_map/(elem_of_list_lookup_1 _ _)[//|i ?]]]; simplify_map_eq.
        eexists _, _. split_and! => //.
        apply list_find_idx_Some. eexists _. split_and!; [done..|] => j[??]/=???; simplify_eq.
        efeed pose proof (NoDup_lookup l.*1 i j); [done| rewrite list_lookup_fmap fmap_Some.. | lia].
        all: naive_solver.
      + move => ? [? /lookup_delete_Some[??]] [?[?/lookup_union_Some[| |]]]; [| |naive_solver].
        { apply map_disjoint_spec => -[??]?? /lookup_kmap_Some. naive_solver. }
        move => /lookup_kmap_Some. naive_solver.
    - by rewrite big_sepM_kmap big_sepM_list_to_map.
  Qed.

  Lemma reg_mapsto_lookup regs r q v :
    regs_ctx regs -∗ r ↦ᵣ{q} v -∗ ⌜regs !! r = Some v⌝.
  Proof.
    rewrite reg_mapsto_eq.
    iIntros "(%rs&%srs&%Hall&%&%&Hregs&?) Hreg".
    iDestruct (ghost_map_lookup with "Hregs Hreg") as %?. iPureIntro.
    by apply: Hall.
  Qed.

  Lemma reg_mapsto_update regs r v v' :
    regs_ctx regs -∗ r ↦ᵣ v ==∗ regs_ctx (<[r := v']>regs) ∗ r ↦ᵣ v'.
  Proof.
    iIntros "(%rs&%srs&%Hrs&%Hsrs&%Hdisj&Hregs&?) Hreg". rewrite reg_mapsto_eq.
    iDestruct (ghost_map_lookup with "Hregs Hreg") as %?.
    iMod (ghost_map_update with "Hregs Hreg") as "[Hregs $]". iModIntro.
    iExists _, _. iFrame. iPureIntro. split_and!.
    - apply: map_Forall_insert_2'; simplify_map_eq; [done|].
      apply: map_Forall_impl; [done|] => /= *; by simplify_map_eq.
    - apply: map_Forall_impl'; [done|] => -[n ?]/= ? ? [?[?[?[??]]]]. eexists _, _. split_and!; [|done..].
      destruct (decide (n = r)); simplify_map_eq => //. naive_solver.
    - move => ? /lookup_insert_is_Some'?. naive_solver.
  Qed.

  Lemma struct_reg_mapsto_lookup regs r q v f:
    regs_ctx regs -∗
    r # f ↦ᵣ{q} v -∗
    ⌜∃ l i, regs !! r = Some (RegVal_Struct l) ∧ list_find_idx (λ x, x.1 = f) l = Some i ∧ l !! i = Some (f, v)⌝.
  Proof.
    rewrite struct_reg_mapsto_eq.
    iIntros "(%rs&%srs&%Hrs&%Hsrs&%&Hregs&Hsregs) Hreg".
    iDestruct (ghost_map_lookup with "Hsregs Hreg") as %?. iPureIntro.
    by apply: (Hsrs (_, _)).
  Qed.

  Lemma struct_reg_mapsto_update regs r f v v' l i :
    regs !! r = Some (RegVal_Struct l) →
    list_find_idx (λ x, x.1 = f) l = Some i →
    regs_ctx regs -∗ r # f ↦ᵣ v ==∗ regs_ctx (<[r:=RegVal_Struct (<[i:=(f, v')]> l)]>regs) ∗ r # f ↦ᵣ v'.
  Proof.
    iIntros (? Hl) "(%rs&%srs&%Hrs&%Hsrs&%Hdisj&Hregs&Hsregs) Hreg". rewrite struct_reg_mapsto_eq.
    iDestruct (ghost_map_lookup with "Hsregs Hreg") as %?.
    iMod (ghost_map_update with "Hsregs Hreg") as "[Hsregs $]". iModIntro.
    iExists _, _. iFrame. iPureIntro. split_and!.
    - apply: map_Forall_impl'; [done|] => n ?? /=?.
      destruct (decide (n = r)); simplify_map_eq => //. naive_solver.
    - apply: map_Forall_insert_2'; simplify_map_eq. {
        eexists _, _. split_and! => //.
        - by apply: list_find_idx_insert_eq.
        - rewrite list_lookup_insert //. by apply: list_find_idx_lt. }
      apply: map_Forall_impl; [done|] => -[r' f']/= ? [?[?[?[??]]]] ?; simplify_map_eq.
      destruct (decide (r = r')); simplify_map_eq. 2: naive_solver.
      move: Hl => /list_find_idx_Some[[??]/=[?[??]]].
      eexists _, _. split_and! => //.
      + apply: list_find_idx_insert_neq; [done|naive_solver|done| naive_solver].
      + apply list_lookup_insert_Some. right. naive_solver.
    - move => ?? [? /lookup_insert_is_Some'?]. naive_solver.
  Qed.
End reg.

Section mem.
  Context `{!heapG Σ}.

  Global Instance backed_mem_tl m : Timeless (backed_mem m).
  Proof. rewrite backed_mem_eq /backed_mem_def. by apply _. Qed.

  Global Instance backed_mem_pers m : Persistent (backed_mem m).
  Proof. rewrite backed_mem_eq /backed_mem_def. by apply _. Qed.

  Global Instance mmio_range_tl a l : Timeless (mmio_range a l).
  Proof. rewrite mmio_range_eq /mmio_range_def. by apply _. Qed.

  Global Instance mmio_range_pers a l : Persistent (mmio_range a l).
  Proof. rewrite mmio_range_eq /mmio_range_def. by apply _. Qed.

  Global Instance mem_mapsto_byte_tl γ a q v : Timeless (mem_mapsto_byte γ a q v).
  Proof. rewrite mem_mapsto_byte_eq. by apply _. Qed.

  Global Instance mem_mapsto_tl n a q (v : bv n) : Timeless (a ↦ₘ{q} v).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. by apply _. Qed.

  Global Instance mem_mapsto_array_tl n a q (l : list (bv n)) : Timeless (a ↦ₘ{q}∗ l).
  Proof. rewrite mem_mapsto_array_eq /mem_mapsto_array_def. by apply _. Qed.


  Lemma backed_mem_agree m1 m2 :
    backed_mem m1 -∗ backed_mem m2 -∗ ⌜m1 = m2⌝.
  Proof.
    rewrite backed_mem_eq. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid. by fold_leibniz.
  Qed.

  Lemma mmio_range_intro mem a l :
    0 ≤ l →
    set_Forall (λ a', ¬ (bv_unsigned a ≤ bv_unsigned a' < bv_unsigned a + l)) mem →
    backed_mem mem -∗ mmio_range a l.
  Proof. rewrite mmio_range_eq. iIntros (??) "?". iExists _. by iFrame. Qed.

  Lemma mmio_range_Forall mem a l :
    mem_ctx mem -∗
    mmio_range a l -∗
    ⌜set_Forall (λ a', ¬ (bv_unsigned a ≤ bv_unsigned a' < bv_unsigned a + l)) (dom (gset _) mem)⌝.
  Proof.
    rewrite mmio_range_eq. iIntros "[_ Hbm] [%bm[% [% Hbm']]]".
    by iDestruct (backed_mem_agree with "Hbm Hbm'") as %?; subst.
  Qed.

  Lemma mmio_range_shorten a l a' l' :
    0 ≤ l' →
    bv_unsigned a ≤ bv_unsigned a' →
    bv_unsigned a' + l' ≤ bv_unsigned a + l →
    mmio_range a l -∗
    mmio_range a' l'.
  Proof.
    rewrite mmio_range_eq.
    iIntros (???) "[%m[%[% ?]]]". iExists _. iFrame.
    iPureIntro. split; [done|]. apply: set_Forall_impl; [done|].
    naive_solver lia.
  Qed.

  Lemma mmio_range_lookup mem a l :
    0 < l →
    mem_ctx mem -∗ mmio_range a l -∗ ⌜read_mem mem a (Z.to_N l) = None⌝.
  Proof.
    iIntros (?) "Hmem Ha".
    iDestruct (mmio_range_Forall with "Hmem Ha") as %Hall. iPureIntro.
    rewrite /read_mem/read_mem_list Z2N.id; [|lia].
    apply fmap_None. apply mapM_None_2.
    rewrite -(Z.succ_pred l) bv_seq_succ; [|lia]. left.
    destruct (mem !! a) eqn: Hl; [|done].
    move: Hall. erewrite <-(insert_id mem); [|done].
    rewrite dom_insert_L => /(set_Forall_union_inv_1 _ _ _)/set_Forall_singleton.
    lia.
  Qed.

  Lemma mem_mapsto_byte_lookup mem a q v :
    mem_ctx mem -∗ mem_mapsto_byte heap_mem_name a q v -∗ ⌜mem !! a = Some v⌝.
  Proof. rewrite mem_mapsto_byte_eq. iIntros "[Hmem _]". by iApply ghost_map_lookup. Qed.

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
  Proof.
    iIntros "Hmem Hbyte". iDestruct (mem_mapsto_byte_lookup with "Hmem Hbyte") as %?.
    rewrite mem_mapsto_byte_eq. iDestruct "Hmem" as "[Hmem Hbacked]".
    iMod (ghost_map_update with "Hmem Hbyte") as "[$ $]".
    by rewrite -{1}(insert_id mem a v) // !dom_insert_L.
  Qed.

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
        ⌜read_mem_list mem a (N.of_nat len) = Some (bv_to_little_endian len 8 (bv_unsigned w))⌝.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen) "Hlist". subst.
    iExists _. iSplit; [done|].
    iDestruct (mem_mapsto_byte_lookup_big with "Hmem Hlist") as %Hall.
    iPureIntro. apply mapM_Some. rewrite bv_to_little_endian_length ?Z2Nat.id in Hall; [|lia..].
    by have ->: (Z.of_N (N.of_nat len) = len) by lia.
  Qed.

  Lemma mem_mapsto_lookup n mem a q (w : bv n) :
    mem_ctx mem -∗ a ↦ₘ{q} w -∗
      ⌜∃ len, n = (8 * len)%N ∧ read_mem mem a len = Some (BVN _ w)⌝.
  Proof.
    iIntros "Hmem Ha". rewrite /read_mem.
    iDestruct (mem_mapsto_lookup_list with "Hmem Ha") as %[len [-> Hl]].
    iPureIntro. eexists _. split; [done|]. rewrite Hl /=. f_equal. apply bvn_eq.
    split; [ done|]. rewrite bv_of_to_little_bv //; lia.
  Qed.

  Lemma mem_mapsto_update_list n mem a (w w' : bv n) :
    mem_ctx mem -∗ a ↦ₘ w ==∗
     ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
      mem_ctx (write_mem_list mem a (bv_to_little_endian len 8 (bv_unsigned w'))) ∗ a ↦ₘ w'.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen) "Hlist". subst.
    iExists _. iSplitR; [done|].
    iMod (mem_mapsto_byte_update_big with "Hmem Hlist") as "[$ H]".
    { rewrite !bv_to_little_endian_length; lia. }
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

  Lemma mem_mapsto_array_insert_acc n a (i : nat) (l : list (bv n)) q len v :
    n = (8 * len)%N →
    l !! i = Some v →
    a ↦ₘ{q}∗ l -∗
    bv_add_Z a (i * Z.of_N len) ↦ₘ{q} v ∗
      (∀ v', bv_add_Z a (i * Z.of_N len) ↦ₘ{q} v' -∗ a ↦ₘ{q}∗ (<[i := v']>l)).
  Proof.
    rewrite mem_mapsto_array_eq. iIntros (??) "[%len' [% Ha]]". have ? : len = len' by lia. subst.
    iDestruct (big_sepL_insert_acc with "Ha") as "[$ Ha]"; [done|].
    iIntros (?) "?". iExists _. iSplit; [done|]. by iApply "Ha".
  Qed.

  Lemma mem_mapsto_array_lookup_acc n a (i : nat) (l : list (bv n)) q len v :
    n = (8 * len)%N →
    l !! i = Some v →
    a ↦ₘ{q}∗ l -∗
    bv_add_Z a (i * Z.of_N len) ↦ₘ{q} v ∗
      (bv_add_Z a (i * Z.of_N len) ↦ₘ{q} v -∗ a ↦ₘ{q}∗ l).
  Proof.
    iIntros (??) "Hl". iDestruct (mem_mapsto_array_insert_acc with "Hl") as "[$ Hl]"; [done..|].
    iIntros "Hv". iDestruct ("Hl" with "Hv") as "Hl". by rewrite list_insert_id.
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
