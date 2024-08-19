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

From stdpp Require Import coPset.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From iris.proofmode Require Export tactics.
From stdpp.bitvector Require Import bitvector.
From isla Require Export opsem spec.
Set Default Proof Using "Type".
Import uPred.

Definition instrtblUR : cmra :=
  agreeR (gmapO addr (leibnizO isla_trace)).

Definition backed_memUR : cmra :=
  agreeR (leibnizO (gset addr)).


Class heapG Σ := HeapG {
  heap_instrs_inG :: inG Σ instrtblUR;
  heap_instrs_name : gname;
  heap_regs_inG :: ghost_mapG Σ string valu;
  heap_struct_regs_inG :: ghost_mapG Σ (string * string) valu;
  heap_mem_inG :: ghost_mapG Σ addr byte;
  heap_mem_name : gname;
  heap_backed_mem_inG :: inG Σ backed_memUR;
  heap_backed_mem_name : gname;
  heap_full_trace : list seq_label;
  heap_spec_trace : list seq_label → Prop;
  heap_spec_trace_inG :: inG Σ (dfrac_agreeR specO);
  heap_spec_trace_name : gname;
}.

Class threadG := ThreadG {
  thread_regs_name : gname;
  thread_struct_regs_name : gname;
}.

Definition to_instrtbl : gmap addr isla_trace → instrtblUR :=
  to_agree.

Definition to_backed_mem : gset addr → backed_memUR :=
  to_agree.

Section definitions.
  Context `{!heapG Σ}.

  Definition instr_table_def (i : gmap addr isla_trace) : iProp Σ :=
    own heap_instrs_name (to_instrtbl i).
  Definition instr_table_aux : seal (@instr_table_def). by eexists. Qed.
  Definition instr_table := unseal instr_table_aux.
  Definition instr_table_eq : @instr_table = @instr_table_def :=
    seal_eq instr_table_aux.

  Definition instr_def (a : Z) (i: option isla_trace) : iProp Σ :=
    ∃ instrs b, ⌜Z_to_bv_checked 64 a = Some b⌝ ∗ ⌜instrs !! b = i⌝ ∗ instr_table instrs.
  Definition instr_aux : seal (@instr_def). by eexists. Qed.
  Definition instr := unseal instr_aux.
  Definition instr_eq : @instr = @instr_def :=
    seal_eq instr_aux.

  Definition instr_ctx (intrs : gmap addr isla_trace) : iProp Σ :=
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

  Definition gen_reg_mapsto (γ1 γ2 : gname) (r : reg_kind) (q : frac) (v: valu) : iProp Σ :=
    match r with
    | KindReg r' => reg_mapsto γ1 r' q v
    | KindField r' f' => struct_reg_mapsto γ2 r' f' q v
    end.

  Definition reg_mapsto_pred_def (γ : gname) (r : string) (q : frac) (P: valu → iProp Σ) : iProp Σ :=
    ∃ v, reg_mapsto γ r q v ∗ P v.
  Definition reg_mapsto_pred_aux : seal (@reg_mapsto_pred_def). by eexists. Qed.
  Definition reg_mapsto_pred := unseal reg_mapsto_pred_aux.
  Definition reg_mapsto_pred_eq : @reg_mapsto_pred = @reg_mapsto_pred_def :=
    seal_eq reg_mapsto_pred_aux.

  Definition struct_reg_mapsto_pred_def (γ : gname) (r f : string) (q : frac) (P: valu → iProp Σ) : iProp Σ :=
    ∃ v, struct_reg_mapsto γ r f q v ∗ P v.
  Definition struct_reg_mapsto_pred_aux : seal (@struct_reg_mapsto_pred_def). by eexists. Qed.
  Definition struct_reg_mapsto_pred := unseal struct_reg_mapsto_pred_aux.
  Definition struct_reg_mapsto_pred_eq : @struct_reg_mapsto_pred = @struct_reg_mapsto_pred_def :=
    seal_eq struct_reg_mapsto_pred_aux.

  Definition reg_col `{!threadG} (regs : list (reg_kind * valu_shape)) : iProp Σ :=
    [∗ list] v ∈ regs, ∃ vact, ⌜valu_has_shape vact v.2⌝ ∗ gen_reg_mapsto thread_regs_name thread_struct_regs_name v.1 1 vact.

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

  Definition mmio_range_def (a : Z) (len : Z) : iProp Σ :=
    ∃ bm, ⌜0 ≤ len⌝ ∗ ⌜0 ≤ a ∧ a + len ≤ 2 ^ 64⌝ ∗
          ⌜set_Forall (λ a', ¬ (a ≤ bv_unsigned a' < a + len)) bm⌝ ∗ backed_mem bm.
  Definition mmio_range_aux : seal (@mmio_range_def). by eexists. Qed.
  Definition mmio_range := unseal mmio_range_aux.
  Definition mmio_range_eq : @mmio_range = @mmio_range_def :=
    seal_eq mmio_range_aux.

  Definition mem_mapsto_byte_def (γ : gname) (a : Z) (q : dfrac) (v : byte) : iProp Σ :=
    ∃ a', ⌜Z_to_bv_checked 64 a = Some a'⌝ ∗ a' ↪[ γ ]{q} v.
  Definition mem_mapsto_byte_aux : seal (@mem_mapsto_byte_def). by eexists. Qed.
  Definition mem_mapsto_byte := unseal mem_mapsto_byte_aux.
  Definition mem_mapsto_byte_eq : @mem_mapsto_byte = @mem_mapsto_byte_def :=
    seal_eq mem_mapsto_byte_aux.

  Definition mem_mapsto_def {n} (a : Z) (q : dfrac) (w : bv n) : iProp Σ :=
    ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗ ⌜0 ≤ a ∧ a + len ≤ 2 ^ 64⌝ ∗
    let bytes := bv_to_little_endian len 8 (bv_unsigned w) in
    [∗ list] offset ↦ b ∈ bytes, mem_mapsto_byte heap_mem_name (a + (Z.of_nat offset)) q b.
  Definition mem_mapsto_aux {n} : seal (@mem_mapsto_def n). by eexists. Qed.
  Definition mem_mapsto {n} := unseal (@mem_mapsto_aux n).
  Definition mem_mapsto_eq {n} : @mem_mapsto n = @mem_mapsto_def n :=
    seal_eq mem_mapsto_aux.

  Definition mem_mapsto_array_def {n} (a : Z) (q : dfrac) (l : list (bv n)) : iProp Σ :=
    ∃ len, ⌜n = (len * 8)%N⌝ ∗ ⌜0 ≤ a ∧ a + Z.of_N len * (length l) ≤ 2 ^ 64⌝ ∗
    [∗ list] i↦v∈l, mem_mapsto (a + (i * Z.of_N len)) q v.
  Definition mem_mapsto_array_aux {n} : seal (@mem_mapsto_array_def n). by eexists. Qed.
  Definition mem_mapsto_array {n} := unseal (@mem_mapsto_array_aux n).
  Definition mem_mapsto_array_eq {n} : @mem_mapsto_array n = @mem_mapsto_array_def n :=
    seal_eq mem_mapsto_array_aux.

  Definition mem_mapsto_uninit_def (a : Z) (q : dfrac) (n : Z) : iProp Σ :=
    ∃ nn : nat, ⌜n = nn⌝ ∗ ⌜0 ≤ a ∧ a + n ≤ 2 ^ 64⌝ ∗
    [∗ list] i ↦ _ ∈ replicate nn (), ∃ v : bv 8, mem_mapsto_byte heap_mem_name (a + i) q v.
  Definition mem_mapsto_uninit_aux : seal (@mem_mapsto_uninit_def). by eexists. Qed.
  Definition mem_mapsto_uninit := unseal (@mem_mapsto_uninit_aux).
  Definition mem_mapsto_uninit_eq : @mem_mapsto_uninit = @mem_mapsto_uninit_def :=
    seal_eq mem_mapsto_uninit_aux.

  Definition mem_ctx (mem : mem_map) : iProp Σ :=
    ghost_map_auth heap_mem_name 1 mem ∗ backed_mem (dom mem).

  Definition spec_trace_raw_def (Pκs: spec) : iProp Σ :=
    own heap_spec_trace_name (to_dfrac_agree (A:=specO) (DfracOwn (1/2)) Pκs).
  Definition spec_trace_raw_aux : seal (@spec_trace_raw_def). by eexists. Qed.
  Definition spec_trace_raw := unseal spec_trace_raw_aux.
  Definition spec_trace_raw_eq : @spec_trace_raw = @spec_trace_raw_def :=
    seal_eq spec_trace_raw_aux.

  Definition spec_trace_def (Pκs: spec) : iProp Σ :=
    ∃ Pκs', ⌜Pκs ⊆ Pκs'⌝ ∗ spec_trace_raw Pκs'.
  Definition spec_trace_aux : seal (@spec_trace_def). by eexists. Qed.
  Definition spec_trace := unseal spec_trace_aux.
  Definition spec_trace_eq : @spec_trace = @spec_trace_def :=
    seal_eq spec_trace_aux.

  Definition spec_ctx (κs : list seq_label) : iProp Σ :=
    ∃ Pκs κscur, ⌜heap_full_trace = κscur ++ κs⌝ ∗
    ⌜heap_spec_trace κscur⌝ ∗
    ⌜Pκs ⊆ λ κs, heap_spec_trace (κscur ++ κs)⌝ ∗
    spec_trace_raw Pκs.

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
Notation "r ↦ᵣ{ q } : P" := (reg_mapsto_pred thread_regs_name r q P%I)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q } :  P") : bi_scope.
Notation "r ↦ᵣ: P" := (reg_mapsto_pred thread_regs_name r 1 P%I) (at level 20) : bi_scope.

Notation "r # f ↦ᵣ{ q } v" := (struct_reg_mapsto thread_struct_regs_name r f q v)
  (at level 20, f at level 10, q at level 50, format "r  #  f  ↦ᵣ{ q }  v") : bi_scope.
Notation "r  #  f  ↦ᵣ v" := (struct_reg_mapsto thread_struct_regs_name r f 1 v)
  (at level 20, f at level 10) : bi_scope.
Notation "r # f ↦ᵣ{ q } : P" := (struct_reg_mapsto_pred thread_struct_regs_name r f q P%I)
  (at level 20, f at level 10, q at level 50, format "r  #  f  ↦ᵣ{ q } :  P") : bi_scope.
Notation "r  #  f  ↦ᵣ: P" := (struct_reg_mapsto_pred thread_struct_regs_name r f 1 P%I)
  (at level 20, f at level 10) : bi_scope.

Notation "r ↦ᵣₖ{ q } v" := (gen_reg_mapsto thread_regs_name thread_struct_regs_name r q v)
  (at level 20, q at level 50, format "r  ↦ᵣₖ{ q }  v") : bi_scope.
Notation "r ↦ᵣₖ v" := (gen_reg_mapsto thread_regs_name thread_struct_regs_name r 1 v) (at level 20) : bi_scope.

Notation "a ↦ₘ{ q } v" := (mem_mapsto a q v)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }  v") : bi_scope.
Notation "a ↦ₘ v" := (mem_mapsto a (DfracOwn 1) v) (at level 20) : bi_scope.

Notation "a ↦ₘ{ q }∗ l" := (mem_mapsto_array a q l)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }∗  l") : bi_scope.
Notation "a ↦ₘ∗ l" := (mem_mapsto_array a (DfracOwn 1) l) (at level 20) : bi_scope.

Notation "a ↦ₘ{ q }? n" := (mem_mapsto_uninit a q n)
  (at level 20, q at level 50, format "a  ↦ₘ{ q }?  n") : bi_scope.
Notation "a ↦ₘ? n" := (mem_mapsto_uninit a (DfracOwn 1) n) (at level 20) : bi_scope.

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

  Lemma instr_addr_in_range a i:
    instr a i -∗ ⌜0 ≤ a < bv_modulus 64⌝.
  Proof.
    rewrite instr_eq/instr_def. iDestruct 1 as (??->%Z_to_bv_checked_Some) "?".
    iPureIntro. apply bv_unsigned_in_range.
  Qed.

  Lemma instr_intro ins a i :
    ∀ Hwf,
    ins !! (@BV _ a Hwf) = i →
    instr_table ins -∗ instr a i.
  Proof.
    rewrite instr_eq. iIntros (??) "?". iExists _, _. iFrame.
    iPureIntro. split; [|done].
    unfold Z_to_bv_checked. case_guard => //=.
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

  Lemma instr_lookup_unsigned instrs i (a : bv 64) :
    instr_ctx instrs -∗ instr (bv_unsigned a) i -∗ ⌜instrs !! a = i⌝.
  Proof.
    iIntros "Hctx Hinstr". iDestruct (instr_lookup with "Hctx Hinstr") as %[b [Hb ?]].
    iPureIntro. unfold Z_to_bv_checked in *. case_guard => //=; by simplify_eq/=.
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
        opose proof* (NoDup_lookup l.*1 i j); [done| rewrite list_lookup_fmap fmap_Some.. | lia].
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

  Lemma reg_col_nil :
    reg_col [] ⊣⊢ True.
  Proof. done. Qed.

  Lemma reg_col_cons r s col :
    reg_col ((r, s)::col) ⊣⊢ (∃ v, ⌜valu_has_shape v s⌝ ∗ r ↦ᵣₖ v) ∗ reg_col col.
  Proof. done. Qed.

  Lemma reg_col_lookup regs i s:
    regs !! i = Some s →
    reg_col regs ⊣⊢ ∃ v, ⌜valu_has_shape v s.2⌝ ∗ s.1 ↦ᵣₖ v ∗ reg_col (delete i regs).
  Proof.
    iIntros (?). rewrite /reg_col. erewrite (delete_Permutation regs); [|done] => /=.
    iSplit.
    - iDestruct 1 as "[[%vact [??] ]?]". iExists _. iFrame.
    - iDestruct 1 as (v ?) "[??]". by iFrame.
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
    0 ≤ a →
    a + l ≤ 2 ^ 64 →
    set_Forall (λ a', ¬ (a ≤ bv_unsigned a' < a + l)) mem →
    backed_mem mem -∗ mmio_range a l.
  Proof. rewrite mmio_range_eq. iIntros (????) "?". iExists _. by iFrame. Qed.

  Lemma mmio_range_Forall mem a l :
    mem_ctx mem -∗
    mmio_range a l -∗
    ⌜set_Forall (λ a', ¬ (a ≤ bv_unsigned a' < a + l)) (dom mem)⌝.
  Proof.
    rewrite mmio_range_eq. iIntros "[_ Hbm] [%bm[% [% [% Hbm']]]]".
    by iDestruct (backed_mem_agree with "Hbm Hbm'") as %?; subst.
  Qed.

  Lemma mmio_range_in_range a l :
    mmio_range a l -∗ ⌜0 ≤ a ∧ a + l ≤ 2 ^ 64⌝.
  Proof. rewrite mmio_range_eq. iIntros "[%bm[% [% [% Hbm']]]]". done. Qed.

  Lemma mmio_range_shorten a l a' l' :
    0 ≤ l' →
    a ≤ a' →
    a' + l' ≤ a + l →
    mmio_range a l -∗
    mmio_range a' l'.
  Proof.
    rewrite mmio_range_eq.
    iIntros (???) "[%m[%[% [% ?]]]]". iExists _. iFrame.
    iPureIntro. split; [done|].  split; [lia|]. apply: set_Forall_impl; [done|].
    naive_solver lia.
  Qed.

  Lemma mmio_range_lookup mem a l :
    0 < l →
    mem_ctx mem -∗ mmio_range a l -∗ ⌜read_mem mem a (Z.to_N l) = None⌝.
  Proof.
    iIntros (?) "Hmem Ha".
    iDestruct (mmio_range_in_range with "Ha") as %?.
    iDestruct (mmio_range_Forall with "Hmem Ha") as %Hall. iPureIntro.
    rewrite /read_mem/read_mem_list Z2N.id; [|lia].
    apply fmap_None. apply mapM_None_2.
    rewrite seqZ_cons; [|lia]. left. apply bind_None. right.
    unshelve eexists (@BV 64 a _). { apply bv_wf_in_range. unfold bv_modulus. lia. }
    split; [ by apply Z_to_bv_checked_Some|].
    apply eq_None_ne_Some => ? Hl.
    move: Hall. erewrite <-(insert_id mem); [|done].
    rewrite dom_insert_L => /(set_Forall_union_inv_1 _ _ _)/set_Forall_singleton.
    rewrite /bv_unsigned. lia.
  Qed.

  Lemma mem_mapsto_byte_in_range a v q :
    mem_mapsto_byte heap_mem_name a q v -∗ ⌜0 ≤ a < 2 ^ 64⌝.
  Proof.
    rewrite mem_mapsto_byte_eq. iDestruct 1 as (a' ->%Z_to_bv_checked_Some) "?".
    iPureIntro. apply bv_unsigned_in_range.
  Qed.

  Lemma mem_mapsto_byte_lookup mem a q v :
    mem_ctx mem -∗
    mem_mapsto_byte heap_mem_name a q v -∗
    ⌜∃ a', Z_to_bv_checked 64 a = Some a' ∧ mem !! a' = Some v⌝.
  Proof.
    rewrite mem_mapsto_byte_eq.
    iIntros "[Hmem _] (%a'&%&Hm)". iExists _. iSplit; [done|].
    by iApply (ghost_map_lookup with "Hmem").
  Qed.

  Lemma mem_mapsto_byte_lookup_big mem a q bs :
    mem_ctx mem -∗ ([∗ list] i↦v∈ bs, mem_mapsto_byte heap_mem_name (a + i) q v) -∗
          ⌜Forall2 (λ a v, Z_to_bv_checked 64 a ≫= (mem !!.) = Some v) (seqZ a (length bs)) bs⌝.
  Proof.
    iIntros "Hmem Hl".
    iInduction bs as [|b bs] "IH" forall (a); simpl. { iPureIntro. constructor. }
    iDestruct "Hl" as "[Ha Hl]". rewrite Z.add_0_r.
    iDestruct (mem_mapsto_byte_lookup with "Hmem Ha") as %[?[??]].
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_succ_comm.
    iDestruct ("IH" with "Hmem Hl") as %?.
    iPureIntro. rewrite seqZ_cons ?Z.pred_succ; [|lia]. constructor; [|done].
    apply bind_Some. naive_solver.
  Qed.

  Lemma mem_mapsto_byte_update mem a v v' :
    mem_ctx mem -∗ mem_mapsto_byte heap_mem_name a (DfracOwn 1) v ==∗
      mem_ctx (<[Z_to_bv 64 a := v']> mem) ∗ mem_mapsto_byte heap_mem_name a (DfracOwn 1) v'.
  Proof.
    iIntros "Hmem Hbyte". iDestruct (mem_mapsto_byte_lookup with "Hmem Hbyte") as %[?[?%Z_to_bv_checked_Some ?]].
    rewrite mem_mapsto_byte_eq. iDestruct "Hmem" as "[Hmem Hbacked]".
    iDestruct "Hbyte" as (a' Heq%Z_to_bv_checked_Some) "Hbyte". subst. apply bv_eq in Heq. subst.
    rewrite Z_to_bv_bv_unsigned.
    iMod (ghost_map_update with "Hmem Hbyte") as "[$ ?]".
    rewrite -{1}(insert_id mem a' v) // !dom_insert_L. iFrame.
    by rewrite Z_to_bv_checked_bv_unsigned.
  Qed.

  Lemma mem_mapsto_byte_update_big mem a bs bs' :
    length bs = length bs' →
    mem_ctx mem -∗
    ([∗ list] i↦v∈ bs, mem_mapsto_byte heap_mem_name (a + i) (DfracOwn 1) v) ==∗
    mem_ctx (write_mem_list mem (Z_to_bv 64 a) bs') ∗
    ([∗ list] i↦v∈ bs', mem_mapsto_byte heap_mem_name (a + i) (DfracOwn 1) v).
  Proof.
    iIntros (Hlen) "Hmem Hbs".
    iInduction bs as [|b bs] "IH" forall (a mem bs' Hlen); destruct bs' => //; csimpl in *. { by iFrame. }
    iDestruct "Hbs" as "[Ha Hbs]". rewrite Z.add_0_r.
    iMod (mem_mapsto_byte_update with "Hmem Ha") as "[Hmem $]".
    setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_succ_comm.
    have -> : (bv_add_Z (Z_to_bv 64 a) 1) = (Z_to_bv 64 (Z.succ a)) by bv_solve.
    iApply ("IH" with "[] Hmem Hbs"). iPureIntro. lia.
  Qed.

  Lemma mem_mapsto_byte_to_mapsto a v q :
    mem_mapsto_byte heap_mem_name a q v -∗ a ↦ₘ{q} v.
  Proof.
    iIntros "Hbyte". iDestruct (mem_mapsto_byte_in_range with "Hbyte") as %?.
    rewrite mem_mapsto_eq. iExists 1%nat. iSplit; [done|] => /=. iSplit; [iPureIntro; lia|].
    rewrite Z.add_0_r -(bv_wrap_land 8) bv_wrap_small ?Z_to_bv_bv_unsigned; [| apply bv_unsigned_in_range].
    by iFrame.
  Qed.

  Lemma mem_mapsto_in_range n a (w : bv n) q:
    a ↦ₘ{q} w -∗ ⌜0 ≤ a ∧ a + Z.of_N (n `div` 8) ≤ 2 ^ 64⌝.
  Proof. rewrite mem_mapsto_eq. iDestruct 1 as (len Hlen ?) "Hlist". iPureIntro. subst. lia. Qed.

  Lemma mem_mapsto_n_mult_8 n a (w : bv n) q:
    a ↦ₘ{q} w -∗ ⌜∃ len, n = (8 * len)%N⌝.
  Proof. rewrite mem_mapsto_eq. iDestruct 1 as (len Hlen ?) "Hlist". iPureIntro. naive_solver. Qed.

  Lemma mem_mapsto_lookup_list n mem a (w : bv n) q:
    mem_ctx mem -∗ a ↦ₘ{q} w -∗
    ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
        ⌜read_mem_list mem a (N.of_nat len) = Some (bv_to_little_endian len 8 (bv_unsigned w))⌝.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen ?) "Hlist". subst.
    iExists _. iSplit; [done|].
    iDestruct (mem_mapsto_byte_lookup_big with "Hmem Hlist") as %Hall.
    iPureIntro. apply mapM_Some. rewrite length_bv_to_little_endian ?Z2Nat.id in Hall; [|lia..].
    by have ->: (Z.of_N (N.of_nat len) = len) by lia.
  Qed.

  Lemma mem_mapsto_lookup n mem a q (w : bv n) :
    mem_ctx mem -∗ a ↦ₘ{q} w -∗
      ⌜∃ len, n = (8 * len)%N ∧ read_mem mem a len = Some (bv_to_bvn w)⌝.
  Proof.
    iIntros "Hmem Ha". rewrite /read_mem.
    iDestruct (mem_mapsto_lookup_list with "Hmem Ha") as %[len [-> Hl]].
    iPureIntro. eexists _. split; [done|]. rewrite Hl /=. f_equal. apply bvn_eq.
    split; [ done|]. rewrite Z_to_bv_little_endian_to_bv_to_little_endian //; lia.
  Qed.

  Lemma mem_mapsto_update_list n mem a (w w' : bv n) :
    mem_ctx mem -∗ a ↦ₘ w ==∗
     ∃ len, ⌜n = (8 * N.of_nat len)%N⌝ ∗
      mem_ctx (write_mem_list mem (Z_to_bv 64 a) (bv_to_little_endian len 8 (bv_unsigned w'))) ∗ a ↦ₘ w'.
  Proof.
    rewrite mem_mapsto_eq. iIntros "Hmem". iDestruct 1 as (len Hlen ?) "Hlist". subst.
    iExists _. iSplitR; [done|].
    iMod (mem_mapsto_byte_update_big with "Hmem Hlist") as "[$ H]".
    { rewrite !length_bv_to_little_endian; lia. }
    iExists _. by iFrame.
  Qed.

  Lemma mem_mapsto_update n mem a (w w' : bv n) :
    mem_ctx mem -∗ a ↦ₘ w ==∗
    ∃ len, ⌜n = (8 * len)%N⌝ ∗ mem_ctx (write_mem len mem (Z_to_bv 64 a) (bv_unsigned w')) ∗ a ↦ₘ w'.
  Proof.
    iIntros "Hmem Ha". unfold write_mem.
    iMod (mem_mapsto_update_list with "Hmem Ha") as (len Hlen) "[Hmem Ha]".
    iExists _. iSplitR; [done|]. iFrame.
    by rewrite Nat2N.id.
  Qed.

  Lemma mem_mapsto_array_in_range n a (l : list (bv n)) q:
    a ↦ₘ{q}∗ l -∗ ⌜0 ≤ a ∧ a + Z.of_N (n `div` 8) * length l ≤ 2 ^ 64⌝.
  Proof. rewrite mem_mapsto_array_eq. iDestruct 1 as (len' ? ?) "?". iPureIntro. subst. nia. Qed.

  Lemma mem_mapsto_array_insert_acc n a (i : nat) (l : list (bv n)) q len v :
    n = (8 * len)%N →
    l !! i = Some v →
    a ↦ₘ{q}∗ l -∗
    (a + (i * Z.of_N len)) ↦ₘ{q} v ∗
      (∀ v', (a + (i * Z.of_N len)) ↦ₘ{q} v' -∗ a ↦ₘ{q}∗ (<[i := v']>l)).
  Proof.
    rewrite mem_mapsto_array_eq. iIntros (??) "[%len' [% [% Ha]]]". have ? : len = len' by lia. subst.
    iDestruct (big_sepL_insert_acc with "Ha") as "[$ Ha]"; [done|].
    iIntros (?) "?". iExists _. iSplit; [done|]. rewrite length_insert. iSplit;[done|]. by iApply "Ha".
  Qed.

  Lemma mem_mapsto_array_lookup_acc n a (i : nat) (l : list (bv n)) q len v :
    n = (8 * len)%N →
    l !! i = Some v →
    a ↦ₘ{q}∗ l -∗
    (a + (i * Z.of_N len)) ↦ₘ{q} v ∗
      ((a + (i * Z.of_N len)) ↦ₘ{q} v -∗ a ↦ₘ{q}∗ l).
  Proof.
    iIntros (??) "Hl". iDestruct (mem_mapsto_array_insert_acc with "Hl") as "[$ Hl]"; [done..|].
    iIntros "Hv". iDestruct ("Hl" with "Hv") as "Hl". by rewrite list_insert_id.
  Qed.

  Lemma mem_mapsto_uninit_in_range n a q:
    a ↦ₘ{q}? n -∗ ⌜0 ≤ a ∧ 0 ≤ n ∧ a + n ≤ 2 ^ 64⌝.
  Proof. rewrite mem_mapsto_uninit_eq. iDestruct 1 as (nn ? ?) "?". iPureIntro. lia. Qed.

  Lemma mem_mapsto_uninit_0 a:
    a ↦ₘ? 0 ⊣⊢ ⌜0 ≤ a ≤ 2 ^ 64⌝.
  Proof.
    rewrite mem_mapsto_uninit_eq. iSplit.
    - iDestruct 1 as (???) "?". iPureIntro. lia.
    - iIntros (?). iExists 0%nat => /=. iPureIntro. lia.
  Qed.

  Lemma mem_mapsto_uninit_split ns a q n:
    0 ≤ ns ≤ n →
    a ↦ₘ{q}? n -∗
    a ↦ₘ{q}? ns ∗ (a + ns) ↦ₘ{q}? (n - ns).
  Proof.
    rewrite mem_mapsto_uninit_eq.
    iIntros (?) "[%nn [% [% Hm]]]"; subst.
    rewrite -(take_drop (Z.to_nat ns) (replicate _ _)) big_sepL_app take_replicate drop_replicate.
    iDestruct "Hm" as "[Hm1 Hm2]". iSplitL "Hm1".
    - iExists _. iSplit; [| iSplit; [|done]]; iPureIntro; lia.
    - iExists (nn - Z.to_nat ns)%nat. iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; lia|].
      iApply (big_sepL_impl with "Hm2").
      iIntros "!>" (???) "[%v ?]". rewrite length_replicate. iExists _.
      have -> : (a + (Z.to_nat ns `min` nn + k)%nat) = (a + ns + k) by lia.
      done.
  Qed.

  Lemma mem_mapsto_uninit_combine ns a q n:
    0 ≤ ns ≤ n →
    a ↦ₘ{q}? ns -∗
    (a + ns) ↦ₘ{q}? (n - ns) -∗
    a ↦ₘ{q}? n.
  Proof.
    rewrite mem_mapsto_uninit_eq.
    iIntros (?) "[%nn1 [% [% Hm1]]] [%nn2 [% [% Hm2]]]"; subst.
    iExists (nn1 + nn2)%nat. iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; lia|].
    rewrite replicate_add big_sepL_app. iFrame.
    iApply (big_sepL_impl with "Hm2").
    iIntros "!>" (???) "[%v ?]". rewrite length_replicate. iExists _.
    have -> : (a + nn1 + k) = (a + (nn1 + k)%nat) by lia.
    done.
  Qed.

  Lemma mem_mapsto_uninit_to_mapsto a q n:
    a ↦ₘ{q}? n -∗ ∃ n' (b : (bv n')), ⌜n' = (Z.to_N n * 8)%N⌝ ∗ a ↦ₘ{q} b.
  Proof.
    rewrite mem_mapsto_uninit_eq.
    iIntros "[%nn [% [% Hm]]]"; subst.
    iDestruct (big_sepL_exist with "Hm") as (ls Hlen) "Hm".
    rewrite length_replicate in Hlen. subst.
    iExists _, (Z_to_bv _ (little_endian_to_bv _ ls)). iSplit; [done|].
    rewrite mem_mapsto_eq. iExists (length ls).
    iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; lia|].
    rewrite Z_to_bv_small ?bv_to_little_endian_to_bv //.
    2: { pose proof (little_endian_to_bv_bound 8 ls).
         unfold bv_modulus. rewrite N2Z.inj_mul Z2N.id; lia. }
    iApply (big_sepL_impl' with "Hm"). { by rewrite length_replicate. }
    iIntros "!>" (k ? ? ??) "[%y [% ?]]"; by simplify_eq.
  Qed.

  Lemma mem_mapsto_mapsto_to_uninit a q n (b : bv n):
    a ↦ₘ{q} b -∗ a ↦ₘ{q}? (Z.of_N (n `div` 8)).
  Proof.
    rewrite mem_mapsto_uninit_eq mem_mapsto_eq.
    iIntros "[%len [-> [% Hm]]]". iExists len. iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; lia|].
    iApply (big_sepL_impl' with "Hm"). { rewrite length_replicate length_bv_to_little_endian; lia. }
    iIntros "!>" (k ? ? ??) "?". eauto with iFrame.
  Qed.
End mem.

Section spec.
  Context `{!heapG Σ}.

  Global Instance spec_trace_raw_tl Pκs : Timeless (spec_trace_raw Pκs).
  Proof. rewrite spec_trace_raw_eq. by apply _. Qed.
  Global Instance spec_trace_tl Pκs : Timeless (spec_trace Pκs).
  Proof. rewrite spec_trace_eq. by apply _. Qed.

  Lemma spec_trace_raw_mono Pκs1 Pκs2 :
    (∀ x, Pκs1 x ↔ Pκs2 x) →
    spec_trace_raw Pκs1 ⊢ spec_trace_raw Pκs2.
  Proof.
    rewrite spec_trace_raw_eq /spec_trace_raw_def => ?.
    by have ->: Pκs1 ≡@{specO} Pκs2.
  Qed.

  Lemma spec_trace_mono Pκs1 Pκs2 :
    Pκs2 ⊆ Pκs1 →
    spec_trace Pκs1 ⊢ spec_trace Pκs2.
  Proof.
    rewrite spec_trace_eq /spec_trace_def => ?.
    iDestruct 1 as (Pκs' ?) "Hspec". iExists _. iFrame. iPureIntro. spec_solver.
  Qed.

  Lemma spec_trace_raw_agree Pκs1 Pκs2 :
    spec_trace_raw Pκs1 -∗ spec_trace_raw Pκs2 -∗ ⌜Pκs1 ≡ Pκs2⌝.
  Proof.
    rewrite spec_trace_raw_eq. iIntros "Ht1 Ht2".
    iDestruct (own_valid_2 with "Ht1 Ht2") as %[Hq Ha]%frac_agree_op_valid.
    done.
  Qed.

  Lemma spec_trace_raw_update Pκs1 Pκs2 Pκs :
    spec_trace_raw Pκs1 -∗ spec_trace_raw Pκs2 ==∗ spec_trace_raw Pκs ∗ spec_trace_raw Pκs.
  Proof.
    iIntros "H1 H2".
    iDestruct (spec_trace_raw_agree with "H1 H2") as %Heq.
    iDestruct (spec_trace_raw_mono with "H1") as "H1"; [done|].
    rewrite spec_trace_raw_eq /spec_trace_raw_def.
    iCombine "H1 H2" as "H". rewrite -frac_agree_op Qp.half_half.
    iMod (own_update _ _ (to_frac_agree (A:=specO) 1 Pκs) with "H") as "H".
    { by apply cmra_update_exclusive. }
    rewrite -{1}Qp.half_half frac_agree_op own_op.
    by iFrame.
  Qed.

  Lemma spec_ctx_cons κ κs (Pκs : spec):
    Pκs [κ] →
    spec_ctx (κ :: κs) -∗ spec_trace Pκs ==∗
    spec_ctx κs ∗ spec_trace (λ κs, Pκs (κ::κs)).
  Proof.
    move => Hκ.
    iDestruct 1 as (HPκs'' κscur Hfull Hspec ?) "Hsc".
    rewrite spec_trace_eq. iDestruct 1 as (Pκs' HPκs') "Hs".
    iDestruct (spec_trace_raw_agree with "Hsc Hs") as %HPκs.
    iMod (spec_trace_raw_update with "Hsc Hs") as "[Ht ?]".
    iModIntro. iSplitR "Ht". 2: { iExists (λ κs, Pκs (κ :: κs)). iFrame. iPureIntro => ?. done. }
    iExists _, (κscur ++ [κ]). iFrame. iPureIntro. split_and!.
    - by rewrite -app_assoc -cons_middle.
    - spec_solver.
    - move => ?. rewrite -app_assoc -cons_middle. spec_solver.
  Qed.

End spec.
