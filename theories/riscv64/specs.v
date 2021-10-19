Require Import isla.automation.
Require Import isla.riscv64.arch.
Require Import isla.riscv64.sys_regs.

Definition sd_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (offset : Z) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  (bv_add_Z r2 offset) ↦ₘ? 8 ∗
  ⌜bv_unsigned r2 `mod` 8 = 0⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned r2 + offset < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    (bv_add_Z r2 offset) ↦ₘ r1 ∗
    True
  ).
Global Instance : LithiumUnfold (@sd_spec) := I.

Definition ld_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (offset : Z) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ: λ _,
  R2 ↦ᵣ RVal_Bits r2 ∗
  (bv_add_Z r2 offset) ↦ₘ r1 ∗
  ⌜bv_unsigned r2 `mod` 8 = 0⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned r2 + offset < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    (bv_add_Z r2 offset) ↦ₘ r1 ∗
    True
  ).
Global Instance : LithiumUnfold (@ld_spec) := I.
