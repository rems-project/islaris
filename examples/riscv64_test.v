Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.

Lemma test `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c None -∗
  instr 0x0000000010300010 None -∗
  instr_body 0x0000000010300000 (
    ∃ x11 : bv 64,
    "x10" ↦ᵣ: λ _,
    "x11" ↦ᵣ RVal_Bits x11 ∗
    "misa" # "bits" ↦ᵣ RVal_Bits (bv_0 64) ∗
    spec_trace (sif (bv_unsigned x11 = 1)
               (scons (SInstrTrap [BV{64} 0x0000000010300010]) snil)
               (scons (SInstrTrap [BV{64} 0x000000001030000c]) snil)) ∗
    True
  ).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  admit.
  Unshelve. all: prepare_sidecond.
  - admit.
  - rewrite sif_false //. rename select (_ ≠ x11) into Hx11. contradict Hx11. bv_solve.
  - admit.
  - rewrite sif_true //.
  - admit.
Admitted.
