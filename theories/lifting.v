From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From isla Require Export opsem ghost_state.
Set Default Proof Using "Type".
Import uPred.

Class islaG Σ := IslaG {
  islaG_invG : invG Σ;
  islaG_gen_heapG :> heapG Σ
}.

Instance isla_irisG `{!islaG Σ} : irisG isla_lang Σ := {
  iris_invG := islaG_invG;
  state_interp σ _ κs _ := state_ctx σ κs;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.
Global Opaque iris_invG.

Instance into_val_val e v `{!TCEq (seq_to_val e) (Some v)} : IntoVal e v.
Proof. apply of_to_val. by apply TCEq_eq. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.


Definition wp_asm_def `{!islaG Σ} `{!threadG} (e : trc) : iProp Σ :=
  (∀ θ, ⌜θ.(seq_trace) = e⌝ -∗ ⌜θ.(seq_nb_state) = false⌝ -∗ thread_ctx θ.(seq_regs) -∗
    WP θ {{ _, True }}).
Definition wp_asm_aux `{!islaG Σ} `{!threadG} : seal (@wp_asm_def Σ _ _). by eexists. Qed.
Definition wp_asm `{!islaG Σ} `{!threadG} : trc → iProp Σ := (wp_asm_aux).(unseal).
Definition wp_asm_eq `{!islaG Σ} `{!threadG} : wp_asm = @wp_asm_def Σ _ _ := (wp_asm_aux).(seal_eq).

Notation WPasm := wp_asm.

Definition wp_exp_def `{!islaG Σ} (e : exp) (Φ : valu → iProp Σ) : iProp Σ :=
  (∃ v, ⌜eval_exp e = Some v⌝ ∗ Φ v).
Definition wp_exp_aux `{!islaG Σ} : seal (@wp_exp_def Σ _). by eexists. Qed.
Definition wp_exp `{!islaG Σ} : exp → (valu → iProp Σ ) → iProp Σ := (wp_exp_aux).(unseal).
Definition wp_exp_eq `{!islaG Σ} : wp_exp = @wp_exp_def Σ _ := (wp_exp_aux).(seal_eq).

Notation "'WPexp' e {{ Φ } }" := (wp_exp e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WPexp' e {{ v , Q } }" := (wp_exp e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WPexp'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.

Ltac inv_seq_step :=
  simplify_eq/=;
  lazymatch goal with
  | H : seq_step _ _ _ _ _ _ |- _ => inversion H; clear H
  end;
  simplify_eq/=;
  lazymatch goal with
  | H : trace_step _ _ _ |- _ => inversion H; clear H
  end;
  simplify_eq/=;
  destruct_and?;
  simplify_eq/=.


Section lifting.
  Context `{!islaG Σ} `{!threadG}.

  Lemma wp_asm_unfold e :
    WPasm e ⊣⊢ wp_asm_def e.
  Proof. by rewrite wp_asm_eq. Qed.
  Lemma wp_exp_unfold e Φ:
    WPexp e {{ Φ }} ⊣⊢ wp_exp_def e Φ.
  Proof. by rewrite wp_exp_eq. Qed.

  Lemma wp_next_instr (nPC : addr) bPC_changed a newPC ins :
    a = (if bPC_changed : bool then bv_unsigned nPC else bv_unsigned nPC + instruction_size) →
    bv_of_Z_checked 64 a = Some newPC →
    ins ≠ [] →
    "_PC" ↦ᵣ Val_Bits nPC -∗
    "__PC_changed" ↦ᵣ Val_Bool bPC_changed -∗
    instr a (Some ins) -∗
    (* TODO: We want some receptiveness property here like ⌜∃ i, i ∈ ins ∧ i can execute to the end⌝ *)
    (∀ i, ⌜i ∈ ins⌝ -∗ "_PC" ↦ᵣ Val_Bits newPC -∗ "__PC_changed" ↦ᵣ Val_Bool false -∗ WPasm i) -∗
    WPasm [].
  Proof.
    iIntros (-> Hchecked ?) "HPC Hchanged Hi Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(Hsctx&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ HPC") as %HPC.
    iDestruct (reg_mapsto_lookup with "Hθ Hchanged") as %Hchanged.
    iDestruct (instr_lookup with "Hictx Hi") as %[?[? Hi]]. simplify_eq.
    iSplit. {
      destruct ins => //.
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      split; [done|].
      eexists _, _. rewrite /next_pc HPC Hchanged.
      cbn -[next_pc]. rewrite /bvn_to_bv. cbn -[next_pc]. rewrite decide_left. cbn -[next_pc]. rewrite Hchecked/=.
      split_and!; [done|]. rewrite Hi. split_and!; [done|by left| done].
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?]].
    rewrite /next_pc HPC Hchanged.
    cbn -[next_pc]. rewrite /bvn_to_bv. cbn -[next_pc]. rewrite decide_left. cbn -[next_pc].
    rewrite Hchecked/= => -[[<- <-] ]. rewrite Hi => -[? [??]]. simplify_eq.
    iFrame. iSplitL; [|done].
    iMod (reg_mapsto_update with "Hθ Hchanged") as "[Hθ Hchanged]".
    iMod (reg_mapsto_update with "Hθ HPC") as "[Hθ HPC]".
    iApply ("Hcont" with "[//] HPC Hchanged"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_next_instr_extern (nPC : addr) bPC_changed a newPC κs:
    a = (if bPC_changed : bool then bv_unsigned nPC else bv_unsigned nPC + instruction_size) →
    bv_of_Z_checked 64 a = Some newPC →
    head κs = Some (SInstrTrap newPC) →
    "_PC" ↦ᵣ Val_Bits nPC -∗
    "__PC_changed" ↦ᵣ Val_Bool bPC_changed -∗
    instr a None -∗
    spec_trace κs -∗
    WPasm [].
  Proof.
    iIntros (-> Hchecked ?) "HPC Hchanged Hi Hspec". setoid_rewrite wp_asm_unfold.
    iIntros ([? regs ?]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(Hsctx&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ HPC") as %HPC.
    iDestruct (reg_mapsto_lookup with "Hθ Hchanged") as %Hchanged.
    iDestruct (instr_lookup with "Hictx Hi") as %[?[? Hi]]. simplify_eq.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      split; [done|].
      eexists _, _. rewrite /next_pc HPC Hchanged.
      cbn -[next_pc]. rewrite /bvn_to_bv. cbn -[next_pc]. rewrite decide_left. cbn -[next_pc]. rewrite Hchecked/=.
      split_and!; [done|]. rewrite Hi. done.
    }
    iIntros "!>" (????). iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?]].
    rewrite /next_pc HPC Hchanged.
    cbn -[next_pc]. rewrite /bvn_to_bv. cbn -[next_pc]. rewrite decide_left. cbn -[next_pc].
    rewrite Hchecked/= => -[[<- <-] ]. rewrite Hi => -[? ?].
    destruct regs, κs => //. simplify_eq/=.
    iMod (spec_ctx_cons with "Hsctx Hspec") as "[??]". iModIntro.
    iFrame. iSplitL; [|done].
    by iApply wp_value.
    Unshelve. apply: [].
  Qed.

  Lemma wp_read_reg_acc r v v' v'' vread ann es q al:
    read_accessor al v' = Some v'' →
    read_accessor al v = Some vread →
    r ↦ᵣ{q} v' -∗
    (⌜vread = v''⌝ -∗ r ↦ᵣ{q} v' -∗ WPasm es) -∗
    WPasm (ReadReg r al v ann :: es).
  Proof.
    iIntros (??) "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _, _. split_and! => //. by right.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[?[?[?[?[[??]|?]]]]]]]]]; simplify_eq/=. 2: {
      iFrame. iSplitL; [|done]. by iApply wp_value.
    }
    unfold register_name in *. simplify_eq/=.
    iFrame; iSplitL; [|done].
    iApply ("Hcont" with "[//] Hr"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_read_reg r v v' ann es q:
    r ↦ᵣ{q} v' -∗
    (⌜v = v'⌝ -∗ r ↦ᵣ{q} v' -∗ WPasm es) -∗
    WPasm (ReadReg r [] v ann :: es).
  Proof. by apply: wp_read_reg_acc. Qed.

  Lemma wp_write_reg_acc r v v' v'' vnew ann es al:
    read_accessor al v = Some vnew →
    write_accessor al v' vnew = Some v'' →
    r ↦ᵣ v' -∗
    (r ↦ᵣ v'' -∗ WPasm es) -∗
    WPasm (WriteReg r al v ann :: es).
  Proof.
    iIntros (? ?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _, _. done.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
    unfold register_name in *. simplify_eq.
    iFrame; iSplitL; [|done].
    iMod (reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]".
    iApply ("Hcont" with "Hr"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_write_reg r v v' ann es:
    r ↦ᵣ v' -∗
    (r ↦ᵣ v -∗ WPasm es) -∗
    WPasm (WriteReg r [] v ann :: es).
  Proof. by apply: wp_write_reg_acc. Qed.


  Lemma wp_read_mem n len a vread (vmem : bv n) es ann kind tag q:
    n = (8 * len)%N →
    a ↦ₘ{q} vmem -∗
    (⌜vread = vmem⌝ -∗ a ↦ₘ{q} vmem -∗ WPasm es) -∗
    WPasm (ReadMem (Val_Bits (BVN n vread)) kind (Val_Bits (BVN 64 a)) len tag ann :: es).
  Proof.
    iIntros (?) "Hm Hcont". setoid_rewrite wp_asm_unfold. subst.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
    have ? : len' = len by lia. subst.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |].
      naive_solver.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[?[?[?[[??]|?]]]]]]]]]; simplify_eq/=. 2:{
      iFrame. iSplitL; [|done]. by iApply wp_value.
    }
    iFrame. iSplit; [|done].
    iApply ("Hcont" with "[] [Hm]"); done.
  Qed.

  Lemma wp_write_mem n len a (vold vnew : bv n) es ann kind tag:
    n = (8 * len)%N →
    a ↦ₘ vold -∗
    (a ↦ₘ vnew -∗ WPasm es) -∗
    WPasm (WriteMem (Val_Bool true) kind (Val_Bits (BVN 64 a)) (Val_Bits (BVN n vnew)) len tag ann :: es).
  Proof.
    iIntros (?) "Hm Hcont". subst. setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
    have ? : len' = len by lia. subst.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |].
      naive_solver.
    }
    iIntros "!>" (????). iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[?[?[?[??]]]]]]]]]; simplify_eq/=.
    iMod (mem_mapsto_update with "Hmem Hm") as (len' ?) "[Hmem Hm]".
    have ? : len' = len by lia. subst. iFrame.
    iModIntro. iSplitL; [|done].
    by iApply ("Hcont" with "Hm").
  Qed.

  Lemma wp_branch_address v es ann:
    WPasm es -∗
    WPasm (BranchAddress v ann :: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_declare_const_bv v es ann b:
    (∀ n Heq, WPasm ((subst_event v (Val_Bits (BV b n Heq))) <$> es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done|done|].
    iFrame.
    Unshelve. 1: exact 0.
    split; [done|]. apply: Z.pow_pos_nonneg; lia.
  Qed.

  Lemma wp_define_const n es ann e:
    WPexp e {{ v, WPasm ((subst_event n v) <$> es) }} -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof.
    rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
    rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done|done|].
    iFrame.
  Qed.

End lifting.

Section exp_lifting.
  Context `{!islaG Σ}.

  Lemma wpe_wand e Φ1 Φ2:
    WPexp e {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WPexp e {{ Φ2 }}.
  Proof.
    rewrite !wp_exp_unfold. iDestruct 1 as (??) "?". iIntros "Hv".
    iExists _. iSplit; [done|]. by iApply "Hv".
  Qed.

  Lemma wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. rewrite wp_exp_unfold. iIntros "?". iExists _. by iFrame. Qed.

  Lemma wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPexp (Manyop op es ann) {{ Φ }}.
  Proof.
    rewrite -{2}(app_nil_l es).
    have : Forall2 (λ e v, eval_exp e = Some v) [] [] by constructor.
    move: (@nil exp) => es'.
    move: {1 3}(@nil valu) => vs Hall.
    iIntros "Hes".
    iInduction es as [|e es] "IH" forall (es' vs Hall) => /=.
    - rewrite right_id wp_exp_unfold.
      iDestruct "Hes" as (v Hv) "HΦ".
      iExists _. iFrame. iPureIntro. simpl.
      erewrite mapM_Some_2; [|done]. done.
    - rewrite wp_exp_unfold.
      iDestruct "Hes" as (v Hv) "HΦ".
      rewrite (cons_middle e) !app_assoc.
      iApply ("IH"); [ | done].
      iPureIntro. apply: Forall2_app; [done|].
      constructor; [done|]. constructor.
  Qed.

  Lemma wpe_unop op e Φ ann:
    WPexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPexp (Unop op e ann) {{ Φ }}.
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (? Hv ??) "HΦ".
    rewrite wp_exp_unfold. iExists _ => /=. iFrame. by rewrite Hv /=.
  Qed.

  Lemma wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (? Hv1) "He2".
    rewrite wp_exp_unfold. iDestruct "He2" as (? Hv2 ? Hv) "HΦ".
    rewrite wp_exp_unfold. iExists _ => /=. iFrame. by rewrite Hv1 Hv2 /=.
  Qed.

  Lemma wpe_ite e1 e2 e3 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, WPexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPexp (Ite e1 e2 e3 ann) {{ Φ }}.
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (? Hv1) "He2".
    rewrite wp_exp_unfold. iDestruct "He2" as (? Hv2) "He3".
    rewrite wp_exp_unfold. iDestruct "He3" as (? Hv3 ? Hv) "HΦ".
    rewrite wp_exp_unfold. iExists _ => /=. iFrame. iPureIntro. simplify_eq.
    rewrite Hv1 Hv2 Hv3. by case_match.
  Qed.

End exp_lifting.
