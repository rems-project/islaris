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

  Lemma wp_next_instr nPC bPC_changed a newPC newPC_changed ins :
    next_pc nPC bPC_changed = Some (a, newPC, newPC_changed) →
    ins ≠ [] →
    "_PC" ↦ᵣ Val_Bits nPC -∗
    "__PC_changed" ↦ᵣ Val_Bool bPC_changed -∗
    instr a ins -∗
    (∀ i, ⌜i ∈ ins⌝ -∗ "_PC" ↦ᵣ newPC -∗ "__PC_changed" ↦ᵣ newPC_changed -∗ WPasm i) -∗
    WPasm [].
  Proof.
    iIntros (Hnext ?) "HPC Hchanged Hi Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ HPC") as %HPC.
    iDestruct (reg_mapsto_lookup with "Hθ Hchanged") as %Hchanged.
    iDestruct (instr_lookup with "Hictx Hi") as %Hi.
    iSplit. {
      destruct ins => //.
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _. rewrite /next_pc_regs HPC Hchanged. cbn -[next_pc]. rewrite Hnext/=.
      split_and!; [done| done|]. rewrite Hi. split; [by left| done].
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?]].
    rewrite /next_pc_regs HPC Hchanged. cbn -[next_pc]. rewrite Hnext/= => -[[<- <-] [-> ]].
    rewrite Hi => -[? ?].
    iFrame. iSplitL; [|done].
    iMod (reg_mapsto_update with "Hθ HPC") as "[Hθ HPC]".
    iMod (reg_mapsto_update with "Hθ Hchanged") as "[Hθ Hchanged]".
    iApply ("Hcont" with "[//] HPC Hchanged"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_read_reg r v v' ann es q:
    r ↦ᵣ{q} v' -∗
    (⌜v = v'⌝ -∗ r ↦ᵣ{q} v' -∗ WPasm es) -∗
    WPasm (ReadReg r [] v ann :: es).
  Proof.
    iIntros "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    move: (Hr) => /reg_map_lookup_is_local ?.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      case_match; [|done]. by right.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step. case_match; [ destruct_or!; destruct_and! | done];
      unfold register_name in *; simplify_eq.
    all: iFrame; iSplitL; [|done].
    2: { by iApply wp_value. }
    iApply ("Hcont" with "[//] Hr"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_write_reg r v v' ann es:
    r ↦ᵣ v' -∗
    (r ↦ᵣ v -∗ WPasm es) -∗
    WPasm (WriteReg r [] v ann :: es).
  Proof.
    iIntros "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    move: (Hr) => /reg_map_lookup_is_local ?.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      by case_match.
    }
    iIntros "!>" (????). iMod "HE" as "_". iModIntro.
    inv_seq_step. case_match; [ destruct_and! | done];
      unfold register_name in *; simplify_eq.
    iFrame; iSplitL; [|done].
    iMod (reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]".
    iApply ("Hcont" with "Hr"); [done|done|].
    iFrame.
  Qed.

  Lemma wp_branch_address v es ann:
    WPasm es -∗
    WPasm (BranchAddress v ann :: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
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
    (∀ n, WPasm ((subst_event v (Val_Bits [BV{b} n])) <$> es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
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
    Unshelve. apply: inhabitant.
  Qed.

  Lemma wp_define_const n es ann e:
    WPexp e {{ v, WPasm ((subst_event n v) <$> es) }} -∗
    WPasm (Smt (DefineConst n e) ann :: es).
  Proof.
    rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
    rewrite wp_asm_unfold.
    iIntros ([???]) "/= -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(%&Hictx)".
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

  Lemma wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. rewrite wp_exp_unfold. iIntros "?". iExists _. by iFrame. Qed.

End exp_lifting.
