Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.

Definition misa_bits : bv 64 :=
  [BV{64}0x800000000015312d].

Definition riscv_test_spec (x11 : bv 64) : spec :=
  (sif (bv_unsigned x11 = 1)
               (scons (SInstrTrap [BV{64} 0x0000000010300010]) snil)
               (scons (SInstrTrap [BV{64} 0x000000001030000c]) snil)).

Lemma riscv_test `{!islaG Σ} `{!threadG} (x11 : bv 64):
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c None -∗
  instr 0x0000000010300010 None -∗
  instr_body 0x0000000010300000 (
    "x10" ↦ᵣ: λ _,
    "x11" ↦ᵣ RVal_Bits x11 ∗
    "misa" ↦ᵣ RegVal_Struct [("bits", RVal_Bits misa_bits)] ∗
    spec_trace (riscv_test_spec x11) ∗
    True
  ).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  - rewrite /riscv_test_spec sif_false //. rename select (_ ≠ x11) into Hx11. contradict Hx11. bv_solve.
  - rewrite /riscv_test_spec sif_true //.
Qed.

Definition riscv_test_regs (x10 x11 : bv 64) : reg_map :=
    <[ "PC" := RVal_Bits [BV{64} 0x0000000010300000] ]> $
    <[ "x10" := RVal_Bits x10 ]> $
    <[ "x11" := RVal_Bits x11 ]> $
    <[ "misa" := RegVal_Struct [("bits", RVal_Bits misa_bits)] ]> $
    ∅.

Definition riscv_test_state_global := {|
    seq_instrs :=
    <[ [BV{64} 0x0000000010300000] := a0]> $
    <[ [BV{64} 0x0000000010300004] := a4]> $
    <[ [BV{64} 0x0000000010300008] := a8]> $
    ∅;
    seq_mem := ∅
|}.

Lemma riscv_test_adequate x10 x11 κs n t2 σ2:
  nsteps n (initial_local_state <$> [riscv_test_regs x10 x11],
            riscv_test_state_global) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧ riscv_test_spec x11 κs.
Proof.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  { unfold riscv_test_spec. destruct (decide ((bv_unsigned x11 = 1))); spec_solver. }
  iIntros (?) "#Hi #Hbm Hspec /= !>". iSplitL => //.
  iIntros (?).
  do 4 (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(?&?&?&?&?)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hctx". iModIntro. iFrame.
  iApply (wp_next_instr_pre with "[$] []").
  - iApply (riscv_test x11).
    all: try by unshelve iApply (instr_intro with "Hi").
  - repeat liAStep.
Qed.
