From stdpp Require Import coPset.
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export tactics.
From isla Require Export opsem.
Set Default Proof Using "Type".
Import uPred.

Class heapG Σ := HeapG {
  heap_instrs_inG :> ghost_mapG Σ addr (list trc);
  heap_instrs_name : gname;
  heap_regs_inG :> ghost_mapG Σ string valu;
}.

Class threadG := ThreadG {
  thread_regs_name : gname;
}.

Section definitions.
  Context `{!heapG Σ}.

  Definition instr_def (a : addr) (i: list trc) : iProp Σ :=
    a ↪[ heap_instrs_name ]□ i.
  Definition instr_aux : seal (@instr_def). by eexists. Qed.
  Definition instr := unseal instr_aux.
  Definition instr_eq : @instr = @instr_def :=
    seal_eq instr_aux.

  Definition instr_ctx (intrs : gmap addr (list trc)) : iProp Σ :=
    ghost_map_auth heap_instrs_name 1 intrs.

  Definition reg_mapsto_def (γ : gname) (r : string) (q : frac) (v: valu) : iProp Σ :=
    r ↪[ γ ]{# q} v.
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). by eexists. Qed.
  Definition reg_mapsto := unseal reg_mapsto_aux.
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def :=
    seal_eq reg_mapsto_aux.

  Definition regs_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    ghost_map_auth thread_regs_name 1 (reg_map_to_gmap regs).

  Definition state_ctx (σ : seq_global_state) (κs : list seq_label) : iProp Σ :=
    ⌜True⌝ ∗
    instr_ctx σ.(seq_instrs).

  Definition thread_ctx `{!threadG} (regs : reg_map) : iProp Σ :=
    regs_ctx regs.

End definitions.

Notation "r ↦ᵣ{ q } v" := (reg_mapsto thread_regs_name r q v)
  (at level 20, q at level 50, format "r  ↦ᵣ{ q }  v") : bi_scope.
Notation "r ↦ᵣ v" := (reg_mapsto thread_regs_name r 1 v) (at level 20) : bi_scope.

Section instr.
  Context `{!heapG Σ}.
  Global Instance instr_pers a i : Persistent (instr a i).
  Proof. rewrite instr_eq. by apply _. Qed.

  Global Instance instr_tl a i : Timeless (instr a i).
  Proof. rewrite instr_eq. by apply _. Qed.

  Lemma instr_lookup instrs a i :
    instr_ctx instrs -∗ instr a i -∗ ⌜instrs !! a = Some i⌝.
  Proof. rewrite instr_eq. by apply ghost_map_lookup. Qed.

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
    iDestruct (ghost_map_lookup with "Hregs Hreg") as %?.
    by rewrite -reg_map_to_gmap_lookup.
  Qed.

  Lemma reg_mapsto_update `{!threadG} regs r v v' :
    regs_ctx regs -∗ r ↦ᵣ v ==∗ regs_ctx (<[r := v']>regs) ∗ r ↦ᵣ v'.
  Proof.
    iIntros "Hregs Hreg".
    iDestruct (reg_mapsto_lookup with "Hregs Hreg") as %?.
    rewrite reg_mapsto_eq.
    iMod (ghost_map_update with "Hregs Hreg") as "[? $]".
    by erewrite reg_map_to_gmap_insert.
  Qed.
End reg.
