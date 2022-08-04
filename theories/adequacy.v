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
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap dfrac_agree.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From isla Require Export ghost_state lifting.
Set Default Proof Using "Type".

Class islaPreG Σ := PreIslaG {
  isla_pre_invG :> invGpreS Σ;
  heap_pre_instrs_inG :> inG Σ (instrtblUR);
  heap_pre_regs_inG :> ghost_mapG Σ string valu;
  heap_pre_struct_regs_inG :> ghost_mapG Σ (string * string) valu;
  heap_pre_mem_inG :> ghost_mapG Σ addr byte;
  heap_pre_backed_mem_inG :> inG Σ (backed_memUR);
  heap_pre_spec_inG :> inG Σ (dfrac_agreeR specO);
}.

Definition islaΣ : gFunctors :=
  #[invΣ; GFunctor (constRF instrtblUR);
   ghost_mapΣ string valu;
   ghost_mapΣ (string * string) valu;
   ghost_mapΣ addr byte;
   GFunctor (constRF backed_memUR);
   GFunctor (dfrac_agreeR specO)].

Global Instance subG_islaPreG {Σ} : subG islaΣ Σ → islaPreG Σ.
Proof. solve_inG. Qed.

Definition initial_local_state `{!Arch} (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := arch_pc_reg;
  seq_nb_state := false;
|}.

Lemma isla_adequacy Σ `{!Arch} `{!islaPreG Σ} (instrs : gmap addr isla_trace) (mem : mem_map) (regs : list reg_map) (Pκs : spec) t2 σ2 κs n:
  Pκs [] →
  (∀ {HG : islaG Σ},
    ⊢ instr_table instrs -∗ backed_mem (dom mem) -∗ spec_trace Pκs -∗ ([∗ map] a↦b∈mem, bv_unsigned a ↦ₘ b)
    ={⊤}=∗ [∗ list] rs ∈ regs, ∀ (_ : threadG), ([∗ map] r↦v∈rs, r ↦ᵣ v) -∗ WPasm tnil) →
  nsteps n (initial_local_state <$> regs, {| seq_instrs := instrs; seq_mem := mem |}) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ Pκs κs.
Proof.
  move => ? Hwp.
  apply: wp_strong_adequacy => ?.
  set i := to_instrtbl instrs.
  set bm := to_backed_mem (dom mem).
  iMod (own_alloc (i)) as (γi) "#Hi" => //.
  iMod (own_alloc (bm)) as (γbm) "#Hb" => //.
  iMod (own_alloc (to_frac_agree (A:= _ -d> _) (1/2 + 1/2) Pκs)) as (γs) "Hs" => //.
  rewrite frac_agree_op. iDestruct "Hs" as "[Hs1 Hs2]".
  iMod (ghost_map_alloc mem) as (γm) "[Hm1 Hm2]".

  set (HheapG := HeapG _ _ γi _ _ _ γm _ γbm κs Pκs _ γs).
  set (HislaG := IslaG _ _ HheapG).
  iAssert (instr_table instrs) as "#His". { by rewrite instr_table_eq. }
  iAssert (backed_mem (dom mem)) as "#Hbm". { by rewrite backed_mem_eq. }

  iMod (Hwp HislaG with "His Hbm [Hs1] [Hm2]") as "Hwp". {
    rewrite spec_trace_eq. iExists _. rewrite spec_trace_raw_eq. by iFrame.
  } {
    iApply (big_sepM_impl with "Hm2"). iIntros "!>" (a b ?) "Ha".
    iApply mem_mapsto_byte_to_mapsto. rewrite mem_mapsto_byte_eq.
    iExists _. iFrame. by rewrite Z_to_bv_checked_bv_unsigned.
  }
  iModIntro.
  iExists _, (replicate (length regs) (λ _, True%I)), _, _.
  iSplitL "Hs2 Hm1"; last first; [iSplitL|].
  - rewrite big_sepL2_replicate_r ?fmap_length // big_sepL_fmap.
    iApply (big_sepL_impl with "Hwp").
    iIntros "!>" (? rs ?) "Hwp".
    iMod (ghost_map_alloc (rs)) as (γr) "[Hr1 Hr2]".
    iMod (ghost_map_alloc (∅ : gmap (string * string) valu)) as (γsr) "[Hsr1 Hsr2]".
    set (HthreadG := ThreadG γr γsr).
    setoid_rewrite wp_asm_unfold.
    iApply ("Hwp" with "[Hr2]"); [|done..|].
    + iApply (big_sepM_impl with "Hr2").
      iIntros "!>" (???) "?". by rewrite reg_mapsto_eq.
    + iExists _, _. iFrame. iPureIntro. split_and! => //.
      * move => /=. naive_solver.
      * move => ?? [?[??]]. simplify_map_eq.
  - iIntros (?????) "(Hspec&?) ? ?".
    iApply fupd_mask_intro; [done|]. iIntros "_".
    iDestruct "Hspec" as (Pκs' ? Hκs Hspec ?) "?".
    simpl in *. subst.
    iPureIntro. split; [naive_solver|].
    by rewrite right_id_L.
  - simpl. iFrame "His Hbm". iFrame. iExists _, [] => /=.
    rewrite spec_trace_raw_eq. by iFrame.
Qed.
