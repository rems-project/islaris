Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.sys_regs.

Definition tmp_registers : list string :=
  ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"].

Definition c_call `{!islaG Σ} `{!threadG} (stack_size : Z) (P : list valu → bv 64 → ((list valu → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ (sp ret : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (KeyReg r, None)) <$> tmp_registers) ∗
  "R0" ↦ᵣ: λ r0, "R1" ↦ᵣ: λ r1, "R2" ↦ᵣ: λ r2, "R3" ↦ᵣ: λ r3, "R4" ↦ᵣ: λ r4, "R5" ↦ᵣ: λ r5,
  "R6" ↦ᵣ: λ r6, "R7" ↦ᵣ: λ r7, "R8" ↦ᵣ: λ r8, "R19" ↦ᵣ: λ r19, "R20" ↦ᵣ: λ r20, "R21" ↦ᵣ: λ r21,
  "R22" ↦ᵣ: λ r22, "R23" ↦ᵣ: λ r23, "R24" ↦ᵣ: λ r24, "R25" ↦ᵣ: λ r25, "R26" ↦ᵣ: λ r26, "R27" ↦ᵣ: λ r27,
  "R28" ↦ᵣ: λ r28, "R29" ↦ᵣ: λ r29,
  "R30" ↦ᵣ RVal_Bits ret ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  ⌜stack_size < bv_unsigned sp < 2 ^ 52⌝ ∗
  bv_sub_Z sp stack_size ↦ₘ? stack_size ∗
  P [r0; r1; r2; r3; r4; r5; r6; r7] sp (λ Q,
  instr_pre (bv_unsigned ret) (
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (KeyReg r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"]) ∗
      reg_col ((λ r, (KeyReg r, None)) <$> tmp_registers) ∗
      "R0" ↦ᵣ: λ r0', "R1" ↦ᵣ: λ r1', "R2" ↦ᵣ: λ r2', "R3" ↦ᵣ: λ r3', "R4" ↦ᵣ: λ r4',
      "R5" ↦ᵣ: λ r5', "R6" ↦ᵣ: λ r6', "R7" ↦ᵣ: λ r7', "R8" ↦ᵣ: λ r8',
      "R19" ↦ᵣ r19 ∗ "R20" ↦ᵣ r20 ∗ "R21" ↦ᵣ r21 ∗ "R22" ↦ᵣ r22 ∗ "R23" ↦ᵣ r23 ∗ "R24" ↦ᵣ r24 ∗
      "R25" ↦ᵣ r25 ∗ "R26" ↦ᵣ r26 ∗ "R27" ↦ᵣ r27 ∗ "R28" ↦ᵣ r28 ∗ "R29" ↦ᵣ r29 ∗
      "R30" ↦ᵣ RVal_Bits ret ∗
      "SP_EL2" ↦ᵣ RVal_Bits sp ∗
      bv_sub_Z sp stack_size ↦ₘ? stack_size ∗
      Q [r0'; r1'; r2'; r3'; r4'; r5'; r6'; r7'; r8']
  )).
Global Instance : LithiumUnfold (@c_call) := I.
