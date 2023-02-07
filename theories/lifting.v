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

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From isla Require Export opsem ghost_state.
Set Default Proof Using "Type".
Import uPred.

Class Arch := {
  arch_pc_reg : register_name;
}.

Class islaG Σ := IslaG {
  islaG_invG : invGS Σ;
  islaG_gen_heapG :> heapG Σ
}.

Global Instance isla_irisG `{!islaG Σ} : irisGS isla_lang Σ := {
  iris_invGS := islaG_invG;
  state_interp σ _ κs _ := state_ctx σ κs;
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.
Global Opaque iris_invGS.

Global Instance into_val_val e v `{!TCEq (seq_to_val e) (Some v)} : IntoVal e v.
Proof. apply of_to_val. by apply TCEq_eq. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.


Definition wp_asm_def `{!Arch} `{!islaG Σ} `{!threadG} (e : isla_trace) : iProp Σ :=
  (∀ θ,
      ⌜θ.(seq_trace) = e⌝ -∗
      ⌜θ.(seq_nb_state) = false⌝ -∗
      ⌜θ.(seq_pc_reg) = arch_pc_reg⌝ -∗
      thread_ctx θ.(seq_regs) -∗
    WP θ {{ _, True }}).
Definition wp_asm_aux `{!Arch} `{!islaG Σ} `{!threadG} : seal (@wp_asm_def _ Σ _ _). by eexists. Qed.
Definition wp_asm `{!Arch} `{!islaG Σ} `{!threadG} : isla_trace → iProp Σ := (wp_asm_aux).(unseal).
Definition wp_asm_eq `{!Arch} `{!islaG Σ} `{!threadG} : wp_asm = @wp_asm_def _ Σ _ _ := (wp_asm_aux).(seal_eq).

Notation WPasm := wp_asm.

Definition wpreadreg_def `{!islaG Σ} `{!threadG}
     (r : register_name) (al : accessor_list) (G : valu → iProp Σ) : iProp Σ :=
  ∀ regs, regs_ctx regs -∗
    ∃ v v', ⌜regs !! r = Some v⌝ ∗ ⌜read_accessor al v = Some v'⌝ ∗ regs_ctx regs ∗ G v'.
Definition wpreadreg_aux `{!islaG Σ} `{!threadG} : seal (@wpreadreg_def _ _ _). by eexists. Qed.
Definition wpreadreg `{!islaG Σ} `{!threadG} : register_name → accessor_list → (valu → iProp Σ) → iProp Σ := (wpreadreg_aux).(unseal).
Definition wpreadreg_eq `{!islaG Σ} `{!threadG} : wpreadreg = @wpreadreg_def _ _ _ := (wpreadreg_aux).(seal_eq).
Notation "'WPreadreg' r '@' al {{ G } }" := (wpreadreg r al G%I)
  (at level 20, r, al, G at level 200, only parsing) : bi_scope.
Notation "'WPreadreg' r '@' al {{ v , G } }" := (wpreadreg r al (λ v, G%I))
  (at level 20, r, al, G at level 200,
   format "'[' 'WPreadreg'  r  '@'  al  '/' '[   ' {{  v ,  G  } } ']' ']'") : bi_scope.

Definition wp_event_def `{!Arch} `{!islaG Σ} `{!threadG} (e : event) (Φ : iProp Σ) : iProp Σ :=
  ∀ t, (Φ -∗ WPasm t) -∗ WPasm (e:t:t).
Definition wp_event_aux `{!Arch} `{!islaG Σ} `{!threadG} : seal (@wp_event_def _ _ _ _). by eexists. Qed.
Definition wp_event `{!Arch} `{!islaG Σ} `{!threadG} : event → iProp Σ → iProp Σ := (wp_event_aux).(unseal).
Definition wp_event_eq `{!Arch} `{!islaG Σ} `{!threadG} : wp_event = @wp_event_def _ _ _ _ := (wp_event_aux).(seal_eq).

Notation "'WPevent' e {{ Φ } }" := (wp_event e Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'WPevent'  e  '/' '[   ' {{  Φ  } } ']' ']'") : bi_scope.

Definition instr_pre'_def `{!Arch} `{!islaG Σ} `{!threadG} (is_later : bool) (a : Z) (P : iProp Σ) : iProp Σ :=
  ▷?is_later (
  P -∗
  ∃ ins,
    instr (bv_wrap 64 a) ins ∗
    match ins with
    | Some t => arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm t
    | None => ∃ Pκs, ⌜Pκs [SInstrTrap (Z_to_bv 64 a)]⌝ ∗ spec_trace Pκs
    end
   ).
Definition instr_pre'_aux `{!Arch} `{!islaG Σ} `{!threadG} : seal (@instr_pre'_def _ Σ _ _). by eexists. Qed.
Definition instr_pre' `{!Arch} `{!islaG Σ} `{!threadG} : bool → Z → iProp Σ → iProp Σ := (instr_pre'_aux).(unseal).
Definition instr_pre'_eq `{!Arch} `{!islaG Σ} `{!threadG} : instr_pre' = @instr_pre'_def _ Σ _ _ := (instr_pre'_aux).(seal_eq).

Notation instr_pre := (instr_pre' true).
Notation instr_body := (instr_pre' false).

Definition wp_exp_def `{!islaG Σ} (e : exp) (Φ : base_val → iProp Σ) : iProp Σ :=
  (∃ v, ⌜eval_exp e = Some v⌝ ∗ Φ v).
Definition wp_exp_aux `{!islaG Σ} : seal (@wp_exp_def Σ _). by eexists. Qed.
Definition wp_exp `{!islaG Σ} : exp → (base_val → iProp Σ ) → iProp Σ := (wp_exp_aux).(unseal).
Definition wp_exp_eq `{!islaG Σ} : wp_exp = @wp_exp_def Σ _ := (wp_exp_aux).(seal_eq).

Notation "'WPexp' e {{ Φ } }" := (wp_exp e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WPexp' e {{ v , Q } }" := (wp_exp e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WPexp'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.

Definition wp_a_exp_def `{!islaG Σ} `{!threadG} (e : a_exp) (Φ : base_val → iProp Σ) : iProp Σ :=
  (∀ regs, thread_ctx regs -∗ ∃ v, ⌜eval_a_exp regs e = Some v⌝ ∗ thread_ctx regs ∗ Φ v).
Definition wp_a_exp_aux `{!islaG Σ} `{!threadG} : seal (@wp_a_exp_def Σ _ _). by eexists. Qed.
Definition wp_a_exp `{!islaG Σ} `{!threadG} : a_exp → (base_val → iProp Σ ) → iProp Σ := (wp_a_exp_aux).(unseal).
Definition wp_a_exp_eq `{!islaG Σ} `{!threadG} : wp_a_exp = @wp_a_exp_def Σ _ _ := (wp_a_exp_aux).(seal_eq).

Notation "'WPaexp' e {{ Φ } }" := (wp_a_exp e%E Φ)
  (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'WPaexp' e {{ v , Q } }" := (wp_a_exp e (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'[' 'WPaexp'  e  '/' '[   ' {{  v ,  Q  } } ']' ']'") : bi_scope.

Ltac inv_seq_step :=
  simplify_eq/=;
  lazymatch goal with
  | H : seq_step _ _ _ _ _ _ |- _ => inversion H; clear H
  end;
  simplify_eq/=;
  lazymatch goal with
  | H : trace_step _ _ _ _ |- _ => inversion H; clear H
  end;
  simplify_eq/=;
  destruct_and?;
  simplify_eq/=.


Section lifting.
  Context `{!Arch} `{!islaG Σ} `{!threadG}.

  (** * Unfolding *)
  Lemma wp_asm_unfold e :
    WPasm e ⊣⊢ wp_asm_def e.
  Proof. by rewrite wp_asm_eq. Qed.
  Lemma wpreadreg_unfold r al Φ:
    WPreadreg r @ al {{ Φ }} ⊣⊢ wpreadreg_def r al Φ.
  Proof. by rewrite wpreadreg_eq. Qed.
  Lemma wp_event_unfold e Φ:
    WPevent e {{ Φ }} ⊣⊢ wp_event_def e Φ.
  Proof. by rewrite wp_event_eq. Qed.
  Lemma wp_exp_unfold e Φ:
    WPexp e {{ Φ }} ⊣⊢ wp_exp_def e Φ.
  Proof. by rewrite wp_exp_eq. Qed.
  Lemma wp_a_exp_unfold e Φ:
    WPaexp e {{ Φ }} ⊣⊢ wp_a_exp_def e Φ.
  Proof. by rewrite wp_a_exp_eq. Qed.

  (** * Proof mode instances *)
  Global Instance elim_modal_bupd_wp_asm p P es :
    ElimModal True p false (|==> P) P (WPasm es) (WPasm es).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd ⊤) fupd_frame_r bi.wand_elim_r.
    rewrite wp_asm_eq.
    iIntros "_ Hs" (???) "?". iMod "Hs". by iApply "Hs".
  Qed.

  Global Instance elim_modal_fupd_wp_asm p P es :
    ElimModal True p false (|={⊤}=> P) P (WPasm es) (WPasm es).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r.
    rewrite wp_asm_eq.
    iIntros "_ Hs" (???) "?". iMod "Hs". by iApply "Hs".
  Qed.

  Global Instance is_except_0_wp_asm es:
    IsExcept0 (WPasm es).
  Proof.
    rewrite /IsExcept0. iIntros "Hwp".
    iAssert (|={⊤}=> WPasm es)%I with "[Hwp]" as ">$".
    by iMod "Hwp" as "$".
  Qed.

  (** * General lemmas *)
  Lemma wp_asm_thread_ctx es :
    (∀ regs, thread_ctx regs ={⊤}=∗ thread_ctx regs ∗ WPasm es) -∗
    WPasm es.
  Proof.
    rewrite wp_asm_eq.
    iIntros "HWP" (????) "Hθ". iMod ("HWP" with "Hθ") as "[? HWP]".
    by iApply "HWP".
  Qed.

  Lemma wp_event_intro e Φ:
    (∀ t, (Φ -∗ WPasm t) -∗ WPasm (e:t:t)) -∗
    WPevent e {{ Φ }}.
  Proof. rewrite wp_event_eq. done. Qed.

  Lemma wp_event_elim e t Φ:
    WPevent e {{ Φ }} -∗
    (Φ -∗ WPasm t) -∗
    WPasm (e:t:t).
  Proof. rewrite wp_event_eq. iIntros "Hwp HΦ". by iApply "Hwp". Qed.

  Lemma wp_event_mono e Φ Φ':
    WPevent e {{ Φ }} -∗
    (Φ -∗ Φ') -∗
    WPevent e {{ Φ' }}.
  Proof.
    rewrite wp_event_eq. iIntros "Hwp HΦ" (t) "HΦ'".
    iApply "Hwp". iIntros "?". iApply "HΦ'". by iApply "HΦ".
  Qed.

  (** * Next instruction & instr_pre'  *)
  Lemma wp_next_instr (PC : bv 64) ins :
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr (bv_unsigned PC) (Some ins) -∗
    ▷ (arch_pc_reg ↦ᵣ RVal_Bits PC -∗ WPasm ins) -∗
    WPasm tnil.
  Proof.
    iIntros "HPC Hi Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(Hsctx&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ HPC") as %HPC.
    iDestruct (instr_lookup_unsigned with "Hictx Hi") as %?.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      split; [done|]. eexists _. by simplify_option_eq.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?]]; unfold register_name in *; simplify_option_eq.
    move => [-> [? ->]].
    iFrame. iSplitL; [|done].
    iApply ("Hcont" with "HPC"); [done|done|done|].
    iFrame.
  Qed.

  Lemma wp_next_instr_extern (PC : bv 64) (Pκs : spec):
    Pκs [SInstrTrap PC] →
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr (bv_unsigned PC) None -∗
    ▷ spec_trace Pκs -∗
    WPasm tnil.
  Proof.
    iIntros (?) "HPC Hi Hspec". setoid_rewrite wp_asm_unfold.
    iIntros ([? regs ? ?]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(Hsctx&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ HPC") as %HPC.
    iDestruct (instr_lookup_unsigned with "Hictx Hi") as %?.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      split; [done|]. eexists _. by simplify_option_eq.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?]]. unfold register_name in *; simplify_option_eq.
    move => [-> ->].
    iMod (spec_ctx_cons with "Hsctx Hspec") as "[??]"; [done|]. iModIntro.
    iFrame. iSplitL; [|done].
    by iApply wp_value.
    Unshelve. apply: tnil.
  Qed.

  Lemma wp_next_instr_pre (PC : bv 64) P l:
    arch_pc_reg ↦ᵣ RVal_Bits PC -∗
    instr_pre' l (bv_unsigned PC) P -∗
    P -∗
    WPasm tnil.
  Proof.
    rewrite instr_pre'_eq. iIntros "HPC Hpre HP".
    iDestruct ("Hpre" with "[$HP]") as (ins) "(>Hinstr & Hwp)".
    rewrite bv_wrap_small; [| by apply bv_unsigned_in_range].
    iDestruct (laterN_le _ 1 with "Hwp") as "Hwp". { destruct l => /=; lia. }
    destruct ins; rewrite Z_to_bv_bv_unsigned.
    - by iApply (wp_next_instr with "HPC Hinstr"); [done..|].
    - iDestruct "Hwp" as (?) "[>% Hwp]".
      by iApply (wp_next_instr_extern with "[$] [$] [$]").
  Qed.

  Lemma instr_pre_wand a1 a2 l1 l2 P Q:
    implb l1 l2 →
    bv_wrap 64 a1 = bv_wrap 64 a2 →
    instr_pre' l1 a1 P -∗
    (Q -∗ P) -∗
    instr_pre' l2 a2 Q.
  Proof.
    rewrite instr_pre'_eq => Himpl Ha.
    iIntros "Hinstr Hwand".
    iApply (laterN_le (Nat.b2n l1)). { destruct l1, l2 => //=. lia. }
    iIntros "!> HQ".
    rewrite Ha. have -> : Z_to_bv 64 a1 = Z_to_bv 64 a2 by apply bv_eq.
    iApply ("Hinstr" with "[HQ Hwand]"). by iApply "Hwand".
  Qed.

  Lemma instr_pre_to_body a P:
    ▷ instr_body a P -∗
    instr_pre a P.
  Proof. rewrite instr_pre'_eq. done. Qed.

  Lemma instr_pre_intro_Some l P ins a:
    instr a (Some ins) -∗
    (P -∗ arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 a) -∗ WPasm ins) -∗
    instr_pre' l a P.
  Proof.
    rewrite instr_pre'_eq.
    iIntros "Hinstr Hwp !> HP".
    iDestruct (instr_addr_in_range with "Hinstr") as %?.
    iExists _. rewrite bv_wrap_small; [|done]. iFrame.
    iIntros "HPC". iApply ("Hwp" with "[$] [$]").
  Qed.

  Lemma instr_pre_intro_None P a l:
    instr a None -∗
    (P -∗ ∃ Pκs, ⌜Pκs [SInstrTrap (Z_to_bv 64 a)]⌝ ∗ spec_trace Pκs) -∗
    instr_pre' l a P.
  Proof.
    rewrite instr_pre'_eq.
    iIntros "Hinstr Hspec !> HP".
    iDestruct (instr_addr_in_range with "Hinstr") as %?.
    iDestruct ("Hspec" with "HP") as (??) "Hspec".
    iExists _. rewrite bv_wrap_small; [|done]. iFrame. iExists _. by iFrame.
  Qed.

  (** * Case distinction  *)
  Lemma wp_cases ts:
    ts ≠ [] →
    (∀ t, ⌜t ∈ ts⌝ -∗ WPasm t) -∗
    WPasm (tcases ts).
  Proof.
    iIntros (?) "Hwp". setoid_rewrite wp_asm_unfold.
    iIntros ([? regs ? ?]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "Hctx".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      destruct ts => //.
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |econstructor; by left|done].
    }
    iIntros "!>" (????) "_". iMod "HE" as "_".
    inv_seq_step. iModIntro.
    iFrame. iSplitL; [|done].
    by iApply "Hwp".
  Qed.

  (** * Registers  *)
  Lemma read_reg_acc r al Φ q v v':
    read_accessor al v = Some v' →
    r ↦ᵣ{q} v -∗
    (r ↦ᵣ{q} v -∗ Φ v') -∗
    WPreadreg r @ al {{ Φ }}.
  Proof.
    rewrite wpreadreg_eq. iIntros (?) "Hr HΦ". iIntros (regs) "Hθ".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    iSpecialize ("HΦ" with "Hr"). iExists _, _. by iFrame.
  Qed.
  Lemma read_reg_nil r Φ q v:
    r ↦ᵣ{q} v -∗
    (r ↦ᵣ{q} v -∗ Φ v) -∗
    WPreadreg r @ [] {{ Φ }}.
  Proof. by apply read_reg_acc. Qed.

  Lemma read_reg_struct r f Φ q v:
    r # f ↦ᵣ{q} v -∗
    (r # f ↦ᵣ{q} v -∗ Φ v) -∗
    WPreadreg r @ [Field f] {{ Φ }}.
  Proof.
    rewrite wpreadreg_eq. iIntros "Hr HΦ". iIntros (regs) "Hθ".
    iDestruct (struct_reg_mapsto_lookup with "Hθ Hr") as %(?&?&?&?&?).
    iSpecialize ("HΦ" with "Hr"). iExists _, _. iFrame. iPureIntro.
    split; [done|]. rewrite /read_accessor/=. by simplify_option_eq.
  Qed.

  Lemma wp_read_reg r v vread ann es al:
    read_accessor al v = Some vread →
    WPreadreg r @ al {{ v', ⌜vread = v'⌝ -∗ WPasm es }} -∗
    WPasm (ReadReg r al v ann :t: es).
  Proof.
    rewrite wp_asm_eq wpreadreg_eq. iIntros (?) "Hr".
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[? Hcont]".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _, _. split_and! => //. by right.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[?[?[?[?[[??]|?]]]]]]]]]; simplify_eq/=. 2: {
      iFrame. iSplitL; [|done]. by iApply wp_value.
    }
    iFrame; iSplitL; [|done].
    iApply ("Hcont" with "[//]"); [done..|].
    iFrame.
  Qed.

  Lemma wp_assume_reg r v ann es al:
    WPreadreg r @ al {{ v', ⌜v = v'⌝ ∗ WPasm es }} -∗
    WPasm (AssumeReg r al v ann :t: es).
  Proof.
    rewrite wp_asm_eq wpreadreg_eq. iIntros "Hr".
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct ("Hr" with "Hθ") as (v' v'' ??) "[Hr [% Hcont]]"; subst.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _. split_and! => //.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step. revert select (∃ x, _) => -[?[?[?[?[??]]]]]; simplify_eq/=.
    iFrame; iSplitL; [|done].
    iApply ("Hcont" with "[]"); [done..|].
    iFrame.
  Qed.

  Lemma wp_write_reg_acc r v v' v'' vnew ann es al:
    read_accessor al v = Some vnew →
    write_accessor al v' vnew = Some v'' →
    r ↦ᵣ v' -∗
    (r ↦ᵣ v'' -∗ WPasm es) -∗
    WPasm (WriteReg r al v ann :t: es).
  Proof.
    iIntros (? ?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (reg_mapsto_lookup with "Hθ Hr") as %Hr.
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _, _. done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
    unfold register_name in *. simplify_eq.
    iFrame; iSplitL; [|done].
    iMod (reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]".
    iApply ("Hcont" with "Hr"); [done..|].
    iFrame.
  Qed.

  Lemma wp_write_reg_struct r v v' vnew ann es f:
    read_accessor [Field f] v = Some vnew →
    r # f ↦ᵣ v' -∗
    (r # f ↦ᵣ vnew -∗ WPasm es) -∗
    WPasm (WriteReg r [Field f] v ann :t: es).
  Proof.
    iIntros (?) "Hr Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (struct_reg_mapsto_lookup with "Hθ Hr") as %(?&?&?&?&?).
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      eexists _, _, _. split_and! => //. rewrite /write_accessor/=. by simplify_option_eq.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[?[?[??]]]]]]]].
    unfold register_name, write_accessor in *. simplify_option_eq.
    iFrame; iSplitL; [|done].
    iMod (struct_reg_mapsto_update with "Hθ Hr") as "[Hθ Hr]"; [done..|].
    iApply ("Hcont" with "Hr"); [done..|].
    iFrame.
  Qed.

  Lemma wp_write_reg r v v' ann es:
    r ↦ᵣ v' -∗
    (r ↦ᵣ v -∗ WPasm es) -∗
    WPasm (WriteReg r [] v ann :t: es).
  Proof. by apply: wp_write_reg_acc. Qed.


  (** * Memory  *)
  Lemma wp_read_mem n len a vread (vmem : bv n) es ann kind tag q:
    n = (8 * len)%N →
    0 < Z.of_N len →
    bv_unsigned a ↦ₘ{q} vmem -∗
    (⌜vread = vmem⌝ -∗ bv_unsigned a ↦ₘ{q} vmem -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (??) "Hm Hcont". setoid_rewrite wp_asm_unfold. subst.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
    have ? : len' = len by lia. subst.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |] => /=.
      eexists _, _, _. simplify_option_eq. naive_solver.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[?[??]]]]]];
      simplify_option_eq; destruct_and!; destruct_or!; destruct_and?; simplify_eq. 2:{
      iFrame. iSplitL; [|done]. by iApply wp_value.
    }
    iFrame. iSplit; [|done].
    iApply ("Hcont" with "[] [Hm]"); done.
  Qed.

  Lemma wp_read_mem_array n len a a' vread vmem (i : nat) (l : list (bv n)) es ann kind tag q:
    n = (8 * len)%N →
    0 < Z.of_N len →
    l !! i = Some vmem →
    a' = bv_unsigned a - (i * Z.of_N len) →
    a' ↦ₘ{q}∗ l -∗
    (⌜vread = vmem⌝ -∗ a' ↦ₘ{q}∗ l -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (??? ->) "Hm Hcont".
    iDestruct (mem_mapsto_array_lookup_acc with "Hm") as "[Hv Hm]"; [done..|].
    rewrite Z.sub_add. iApply (wp_read_mem with "Hv"); [lia..|].
    iIntros (?) "Hl". iApply ("Hcont" with "[//]"). by iApply "Hm".
  Qed.

  Lemma wp_read_mmio n len a (vread : bv _) es ann kind tag (Pκs : spec):
    n = (8 * len)%N →
    0 < Z.of_N len →
    Pκs [SReadMem a vread] →
    mmio_range (bv_unsigned a) (Z.of_N len) -∗
    spec_trace Pκs -∗
    (spec_trace (λ κs, Pκs (SReadMem a vread::κs)) -∗ WPasm es) -∗
    WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iIntros (???) "Hm Hspec Hcont". subst. setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mmio_range_lookup with "Hmem Hm") as %Hread; [done|].
    rewrite N2Z.id in Hread.
    iDestruct (mmio_range_in_range with "Hm") as %?.
    iDestruct (mmio_range_Forall with "Hmem Hm") as %?.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |] => /=.
      eexists _, _, (bv_0 _). simplify_option_eq. naive_solver.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[??]]]]]; simplify_option_eq; destruct_and!; simplify_eq.
    iMod (spec_ctx_cons with "Hctx Hspec") as "[Hctx Hspec]"; [done|].
    iFrame. iModIntro. iSplitL; [|done].
    by iApply ("Hcont" with "Hspec").
  Qed.

  Lemma wp_write_mem n len a (vold vnew : bv n) es ann res kind tag:
    n = (8 * len)%N →
    0 < Z.of_N len →
    bv_unsigned a ↦ₘ vold -∗
    (bv_unsigned a ↦ₘ vnew -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (??) "Hm Hcont". subst. setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mem_mapsto_lookup with "Hmem Hm") as %[len' [??]].
    have ? : len' = len by lia. subst.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |]. simpl.
      eexists _, _, _. simplify_option_eq. naive_solver.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[??]]]]]; simplify_option_eq; destruct_and!; simplify_eq.
    iMod (mem_mapsto_update with "Hmem Hm") as (len' ?) "[Hmem Hm]".
    rewrite Z_to_bv_bv_unsigned. have ? : len' = len by lia. subst. iFrame.
    iModIntro. iSplitL; [|done].
    by iApply ("Hcont" with "Hm").
  Qed.

  Lemma wp_write_mem_array n len a a' vnew (i : nat) (l : list (bv n)) es ann kind res tag:
    n = (8 * len)%N →
    0 < Z.of_N len →
    (i < length l)%nat →
    a' = bv_unsigned a - (i * Z.of_N len) →
    a' ↦ₘ∗ l -∗
    (a' ↦ₘ∗ <[i := vnew]> l -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (??[??]%lookup_lt_is_Some_2 ->) "Hm Hcont".
    iDestruct (mem_mapsto_array_insert_acc with "Hm") as "[Hv Hm]"; [done..|].
    rewrite Z.sub_add. iApply (wp_write_mem with "Hv"); [lia..|].
    iIntros "Hl". iApply ("Hcont"). by iApply "Hm".
  Qed.

  Lemma wp_write_mmio n len a (vnew : bv n) es ann res kind tag (Pκs : spec):
    n = (8 * len)%N →
    0 < Z.of_N len →
    Pκs [SWriteMem a vnew] →
    mmio_range (bv_unsigned a) (Z.of_N len) -∗
    spec_trace Pκs -∗
    (spec_trace (λ κs, Pκs (SWriteMem a vnew::κs)) -∗ WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iIntros (???) "Hm Hspec Hcont". subst. setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ????) "(Hctx&Hictx&Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iDestruct (mmio_range_lookup with "Hmem Hm") as %Hread; [done|].
    rewrite N2Z.id in Hread.
    iDestruct (mmio_range_in_range with "Hm") as %?.
    iDestruct (mmio_range_Forall with "Hmem Hm") as %?.
    iSplit. {
      iPureIntro. eexists _, _, _, _. simpl. econstructor; [done | by econstructor |]. simpl.
      eexists ∅, _, _. simplify_option_eq. naive_solver.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_".
    inv_seq_step.
    revert select (∃ _, _) => -[?[?[?[?[??]]]]]; simplify_option_eq; destruct_and!; simplify_eq.
    iMod (spec_ctx_cons with "Hctx Hspec") as "[Hctx Hspec]"; [done|].
    iFrame. iModIntro. iSplitL; [|done].
    by iApply ("Hcont" with "Hspec").
  Qed.

  (** * Other lifting lemmas  *)
  Lemma wp_branch_address v es ann:
    WPasm es -∗
    WPasm (BranchAddress v ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
  Qed.

  Lemma wp_branch c desc es ann:
    WPasm es -∗
    WPasm (Branch c desc ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
  Qed.

  Lemma wp_declare_const_bv v es ann b:
    (∀ (n : bv b), WPasm (subst_trace (Val_Bits n) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_BitVec b)) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by apply DeclareConstBitVecS'|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
    Unshelve. apply: inhabitant.
  Qed.

  Lemma wp_declare_const_bool v es ann:
    (∀ (b : bool), WPasm (subst_trace (Val_Bool b) v es)) -∗
    WPasm (Smt (DeclareConst v Ty_Bool) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
    Unshelve. exact true.
  Qed.

  Lemma wp_declare_const_enum v es i ann:
    (∀ c, WPasm (subst_trace (Val_Enum (i, c)) v es)) -∗
    WPasm (Smt (DeclareConst v (Ty_Enum i)) ann :t: es).
  Proof.
    iIntros "Hcont". setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx&?)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
    Unshelve. exact: inhabitant.
  Qed.

  Lemma wp_define_const n es ann e:
    WPexp e {{ v, WPasm (subst_trace v n es) }} -∗
    WPasm (Smt (DefineConst n e) ann :t: es).
  Proof.
    rewrite wp_asm_unfold wp_exp_unfold. iDestruct 1 as (v Hv) "Hcont".
    rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "(?&Hictx)".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. eexists _, _, _, _; simpl. econstructor; [done |by econstructor|]; simpl.
      done.
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplitL; [|done].
    iApply ("Hcont"); [done..|].
    iFrame.
  Qed.

  Lemma wp_assert es ann e:
    WPexp e {{ v, ∃ b, ⌜v = Val_Bool b⌝ ∗ (⌜b = true⌝ -∗ WPasm es) }} -∗
    WPasm (Smt (Assert e) ann :t: es).
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (v Hv b ?) "Hcont". subst v.
    rewrite !wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "Hctx".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro. destruct b.
      all: eexists _, _, _, _; econstructor; [done |by econstructor| done].
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplit; [|done].
    destruct b => /=; last by iApply wp_value.
    iApply "Hcont"; [done..|iFrame].
  Qed.

  Lemma wp_assume es ann e:
    WPaexp e {{ v, ⌜v = Val_Bool true⌝ ∗ WPasm es }} -∗
    WPasm (Assume e ann :t: es).
  Proof.
    rewrite wp_a_exp_unfold wp_asm_eq.
    iIntros "Hexp" ([????]) "/= -> -> -> Hθ".
    iDestruct ("Hexp" with "Hθ") as (v ?) "(Hθ&%&Hcont)"; subst.
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "Hctx".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro.
      eexists _, _, _, _; econstructor; [done | by econstructor|done].
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplit; [|done].
    iApply "Hcont"; [done..|iFrame].
  Qed.

  Lemma wp_barrier es v ann:
    WPasm es -∗
    WPasm (Barrier v ann :t: es).
  Proof.
    rewrite wp_asm_eq.
    iIntros "Hcont" ([????]) "/= -> -> -> Hθ".
    iApply wp_lift_step; [done|].
    iIntros (σ1 ??? ?) "Hctx".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iSplit. {
      iPureIntro.
      eexists _, _, _, _; econstructor; [done |by econstructor| done].
    }
    iIntros "!>" (????) "_". iMod "HE" as "_". iModIntro.
    inv_seq_step.
    iFrame; iSplit; [|done].
    iApply "Hcont"; [done..|iFrame].
  Qed.

End lifting.

Section exp_lifting.
  Context `{!islaG Σ} `{!threadG}.

  Lemma wpe_wand e Φ1 Φ2:
    WPexp e {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WPexp e {{ Φ2 }}.
  Proof.
    rewrite !wp_exp_unfold. iDestruct 1 as (??) "?". iIntros "Hv".
    iExists _. iSplit; [done|]. by iApply "Hv".
  Qed.

  Lemma wpae_wand e Φ1 Φ2:
    WPaexp e {{ Φ1 }} -∗
    (∀ v, Φ1 v -∗ Φ2 v) -∗
    WPaexp e {{ Φ2 }}.
  Proof.
    rewrite !wp_a_exp_unfold.
    iIntros "Hexp HΦ" (regs) "Hregs".
    iDestruct ("Hexp" with "Hregs") as (??) "[??]".
    iExists _. iSplit; [done|]. iFrame. by iApply "HΦ".
  Qed.

  Lemma wpe_val v Φ ann:
    Φ v -∗
    WPexp (Val v ann) {{ Φ }}.
  Proof. rewrite wp_exp_unfold. iIntros "?". iExists _. by iFrame. Qed.

  Lemma wpae_var_reg r Φ ann al :
    WPreadreg r @ al {{ v', if v' is RegVal_Base v'' then Φ v'' else False }} -∗
    WPaexp (AExp_Val (AVal_Var r al) ann) {{ Φ }}.
  Proof.
    rewrite wp_a_exp_unfold wpreadreg_eq. iIntros "Hr" (?) "Hregs" => /=.
    iDestruct ("Hr" with "Hregs") as (????) "[? ?]"; subst. case_match => //.
    iExists _ => /=. simplify_option_eq. iSplit; [done|]. by iFrame.
  Qed.

  Lemma wpae_bits b Φ ann:
    Φ (Val_Bits b) -∗
    WPaexp (AExp_Val (AVal_Bits b) ann) {{ Φ }}.
  Proof. rewrite wp_a_exp_unfold. iIntros "?" (?) "?". iExists _. by iFrame. Qed.
  Lemma wpae_bool b Φ ann:
    Φ (Val_Bool b) -∗
    WPaexp (AExp_Val (AVal_Bool b) ann) {{ Φ }}.
  Proof. rewrite wp_a_exp_unfold. iIntros "?" (?) "?". iExists _. by iFrame. Qed.
  Lemma wpae_enum b Φ ann:
    Φ (Val_Enum b) -∗
    WPaexp (AExp_Val (AVal_Enum b) ann) {{ Φ }}.
  Proof. rewrite wp_a_exp_unfold. iIntros "?" (?) "?". iExists _. by iFrame. Qed.

  Lemma wpe_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPexp (Manyop op es ann) {{ Φ }}.
  Proof.
    rewrite -{2}(app_nil_l es).
    have : Forall2 (λ e v, eval_exp e = Some v) [] [] by constructor.
    move: (@nil exp) => es'.
    move: {1 3}(@nil base_val) => vs Hall.
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

  Lemma wpae_manyop op es Φ ann:
    foldr (λ e Ψ, λ vs, WPaexp e {{ v, Ψ (vs ++ [v]) }}) (λ vs, ∃ v, ⌜eval_manyop op vs = Some v⌝ ∗ Φ v) es [] -∗
    WPaexp (AExp_Manyop op es ann) {{ Φ }}.
  Proof.
    rewrite wp_a_exp_unfold.
    iIntros "Hes" (regs) "Hregs".
    rewrite -{2}(app_nil_l es).
    have : Forall2 (λ e v, eval_a_exp regs e = Some v) [] [] by constructor.
    move: (@nil a_exp) => es'.
    move: {1 3}(@nil base_val) => vs Hall.
    iInduction es as [|e es] "IH" forall (es' vs Hall) => /=.
    - rewrite right_id.
      iDestruct "Hes" as (v Hv) "HΦ".
      iExists _. iFrame. iPureIntro. simpl.
      erewrite mapM_Some_2; [|done]. done.
    - rewrite wp_a_exp_unfold.
      iDestruct ("Hes" with "Hregs") as (v Hv) "[Hregs HΦ]".
      rewrite (cons_middle e) !app_assoc.
      iApply ("IH" with "[] HΦ Hregs").
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

  Lemma wpae_unop op e Φ ann:
    WPaexp e {{ v1, ∃ v, ⌜eval_unop op v1 = Some v⌝ ∗ Φ v}} -∗
    WPaexp (AExp_Unop op e ann) {{ Φ }}.
  Proof.
    rewrite !wp_a_exp_unfold. iIntros "Hexp" (?) "Hregs".
    iDestruct ("Hexp" with "Hregs") as (? Hv) "[Hregs [%v' [% HΦ]]]".
    iExists _ => /=. iFrame. by rewrite Hv /=.
  Qed.

  Lemma wpe_binop op e1 e2 Φ ann:
    WPexp e1 {{ v1, WPexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPexp (Binop op e1 e2 ann) {{ Φ }}.
  Proof.
    rewrite wp_exp_unfold. iDestruct 1 as (? Hv1) "He2".
    rewrite wp_exp_unfold. iDestruct "He2" as (? Hv2 ? Hv) "HΦ".
    rewrite wp_exp_unfold. iExists _ => /=. iFrame. by rewrite Hv1 Hv2 /=.
  Qed.

  Lemma wpae_binop op e1 e2 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, ∃ v, ⌜eval_binop op v1 v2 = Some v⌝ ∗ Φ v}} }} -∗
    WPaexp (AExp_Binop op e1 e2 ann) {{ Φ }}.
  Proof.
    rewrite !wp_a_exp_unfold. iIntros "Hexp" (?) "Hregs".
    iDestruct ("Hexp" with "Hregs") as (? Hv1) "[Hregs He2]".
    rewrite wp_a_exp_unfold. iDestruct ("He2" with "Hregs") as (? Hv2) "[Hregs [%v' [% HΦ]]]".
    iExists _ => /=. iFrame. by rewrite Hv1 Hv2 /=.
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

  Lemma wpae_ite e1 e2 e3 Φ ann:
    WPaexp e1 {{ v1, WPaexp e2 {{ v2, WPaexp e3 {{ v3,
       ∃ b, ⌜v1 = Val_Bool b⌝ ∗ Φ (ite b v2 v3)}} }} }} -∗
    WPaexp (AExp_Ite e1 e2 e3 ann) {{ Φ }}.
  Proof.
    rewrite !wp_a_exp_unfold. iIntros "He1" (?) "Hregs".
    iDestruct ("He1" with "Hregs") as (? Hv1) "[Hregs He2]".
    rewrite wp_a_exp_unfold. iDestruct ("He2" with "Hregs") as (? Hv2) "[Hregs He3]".
    rewrite wp_a_exp_unfold. iDestruct ("He3" with "Hregs") as (? Hv3) "[Hregs [%b [% HΦ]]]".
    iExists _ => /=. iFrame. iPureIntro. simplify_eq.
    rewrite Hv1 Hv2 Hv3. by case_match.
  Qed.

End exp_lifting.
