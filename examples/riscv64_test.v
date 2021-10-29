Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.

Definition riscv_test_spec (x11 : bv 64) : spec :=
  (sif (bv_unsigned x11 = 1)
               (scons (SInstrTrap [BV{64} 0x0000000010300018]) snil)
               (scons (SInstrTrap [BV{64} 0x0000000010300014]) snil)).

Lemma riscv_test `{!islaG Σ} `{!threadG} (x2 x11 : bv 64):
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 None -∗
  instr 0x0000000010300018 None -∗
  instr_body 0x0000000010300000 (
    reg_col sys_regs ∗
    "x10" ↦ᵣ: λ _,
    "x2" ↦ᵣ RVal_Bits x2 ∗
    "x11" ↦ᵣ RVal_Bits x11 ∗
    ⌜bv_unsigned x2 `mod` 8 = 0⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned x2 + 8 < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    (bv_unsigned x2 + 8) ↦ₘ? 8 ∗
    spec_trace (riscv_test_spec x11) ∗
    True
  ).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  - rewrite /riscv_test_spec sif_true //. normalize_and_simpl_goal => //; bv_solve.
  - rewrite /riscv_test_spec sif_false. 1: normalize_and_simpl_goal => //; bv_solve.
    rename select (_ ≠ x11) into Hx11. contradict Hx11. bv_solve.
Qed.

Definition riscv_test_regs (mstatus_bits satp x2 x10 x11 : bv 64) : reg_map :=
    <[ "PC" := RVal_Bits [BV{64} 0x0000000010300000] ]> $
    <[ "x2" := RVal_Bits x2 ]> $
    <[ "x10" := RVal_Bits x10 ]> $
    <[ "x11" := RVal_Bits x11 ]> $
    sys_regs_map mstatus_bits satp.

Definition riscv_test_state_global (x2 : bv 64) := {|
    seq_instrs :=
    <[ [BV{64} 0x0000000010300000] := a0]> $
    <[ [BV{64} 0x0000000010300004] := a4]> $
    <[ [BV{64} 0x0000000010300008] := a8]> $
    <[ [BV{64} 0x000000001030000c] := ac]> $
    <[ [BV{64} 0x0000000010300010] := a10]> $
    ∅;
    seq_mem := list_to_map (zip (bv_seq (bv_add_Z x2 8) 8) (replicate 8 (bv_0 8)))
|}.
Local Arguments zip_with : simpl never.
Local Arguments list_to_map : simpl never.

Lemma riscv_test_adequate mstatus_bits satp x2 x10 x11 κs n t2 σ2:
  bv_extract 17 1 mstatus_bits = [BV{1} 0] →
  bv_unsigned x2 `mod` 8 = 0 →
  bv_unsigned x2 + 16 < 2 ^ 64 →
  0x0000000080000000 ≤ bv_unsigned x2 + 8 < 0x0000000080000000 + 0x0000000004000000 →
  nsteps n (initial_local_state <$> [riscv_test_regs mstatus_bits satp x2 x10 x11],
            riscv_test_state_global x2) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ riscv_test_spec x11 κs.
Proof.
  move => ????.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  { unfold riscv_test_spec. destruct (decide ((bv_unsigned x11 = 1))); spec_solver. }
  iIntros (?) "#Hi #Hbm Hspec Hmem /= !>". iSplitL => //. iIntros (?).
  iAssert ((bv_unsigned x2 + 8) ↦ₘ? 8)%I with "[Hmem]" as "?". {
    rewrite big_sepM_list_to_map. 2: { rewrite fst_zip //. by apply NoDup_bv_seq. }
    rewrite /zip_with/=. iClear "Hbm".
    iDestruct "Hmem" as "(Hm1&Hm2&Hm3&Hm4&Hm5&Hm6&Hm7&Hm8&_)".
    rewrite bv_add_Z_0 -!bv_add_Z_add_r !bv_add_Z_unsigned !bv_wrap_small; [|bv_solve..].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm1]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm2]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm3]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm4]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm5]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm6]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm7]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    rewrite -!Z.add_assoc.
    iApply (mem_mapsto_uninit_combine 1 with "[Hm8]"); [done|by iApply (mem_mapsto_mapsto_to_uninit _ _ 8)|].
    by rewrite mem_mapsto_uninit_0.
  }
  do 4 (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(?&?&?&?&Hsys)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hctx".
  iMod (sys_regs_init with "Hctx Hsys") as "[$ Hsys]"; [done|]. iModIntro.
  iApply (wp_next_instr_pre with "[$] []").
  - iApply (riscv_test x2 x11).
    all: try by unshelve iApply (instr_intro with "Hi").
  - repeat liAStep.
Qed.
