From iris.proofmode Require Import tactics.
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From isla Require Import ghost_state lifting.
From iris.program_logic Require Export language.
Set Default Proof Using "Type".

Class islaPreG Σ := PreIslaG {
  isla_pre_invG :> invPreG Σ;
  heap_pre_instrs_inG :> inG Σ (instrtblUR);
  heap_pre_regs_inG :> ghost_mapG Σ string valu;
  heap_pre_spec_inG :> ghost_varG Σ (list seq_label);
}.

Definition islaΣ : gFunctors :=
  #[invΣ; GFunctor (constRF instrtblUR); ghost_mapΣ string valu; ghost_varΣ (list seq_label)].

Instance subG_islaPreG {Σ} : subG islaΣ Σ → islaPreG Σ.
Proof. solve_inG. Qed.

Definition initial_local_state (regs : reg_map) : seq_local_state := {|
  seq_trace := [];
  seq_regs := regs;
  seq_nb_state := false;
|}.

Lemma isla_adequacy Σ `{!islaPreG Σ} (instrs : gmap addr (list trc)) (regs : list reg_map) κsspec t2 σ2 κs n:
  (∀ {HG : islaG Σ},
    ⊢ instr_table instrs -∗ spec_trace κsspec
    ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG), ([∗ map] r↦v∈reg_map_to_gmap rs, r ↦ᵣ v) -∗ WPasm []) →
  nsteps n (initial_local_state <$> regs, {| seq_instrs := instrs |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
  κs `prefix_of` κsspec.
Proof.
  move => Hwp.
  apply: wp_strong_adequacy => ?.
  set i := to_instrtbl instrs.
  iMod (own_alloc (i)) as (γi) "#Hi" => //.
  iMod (ghost_var_alloc κsspec) as (γs) "[Hs1 Hs2]".

  set (HheapG := HeapG _ _ γi _ κs κsspec _ γs).
  set (HislaG := IslaG _ _ HheapG).
  iAssert (instr_table instrs) as "#His". { by rewrite instr_table_eq. }

  iMod (Hwp HislaG with "His [Hs1]") as "Hwp". {
    rewrite spec_trace_eq. iFrame.
  }

  iModIntro.
  iExists NotStuck, _, (replicate (length regs) (λ _, True%I)), _, _.
  iSplitL "Hs2"; last first; [iSplitL|].
  - rewrite big_sepL2_replicate_r ?fmap_length // big_sepL_fmap.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!>" (? rs ?) "Hwp".
    iMod (ghost_map_alloc (reg_map_to_gmap rs)) as (γr) "[Hr1 Hr2]".
    set (HthreadG := ThreadG γr).
    setoid_rewrite wp_asm_unfold.
    iApply ("Hwp" with "[Hr2]"); [|done|done|done].
    iApply (big_sepM_impl with "Hr2").
    iIntros "!>" (???) "?".
      by rewrite reg_mapsto_eq.
  - iIntros (?????) "(Hspec&?) ? ?".
    iApply fupd_mask_intro; [done|]. iIntros "_".
    iDestruct "Hspec" as (? ? Hκs Hspec) "?".
    simpl in *. subst.
    iPureIntro. split; [naive_solver|].
    rewrite right_id. by apply: prefix_app_r.
  - simpl. iFrame "His".
    iExists [], _. by iFrame.
Qed.
