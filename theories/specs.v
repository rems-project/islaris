Require Import isla.automation.
Require Import isla.sys_regs.

Definition sub_R_R_R_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 R3 : string) : iProp Σ :=
  ∃ (r2 r3 : bv 64),
  R1 ↦ᵣ: λ r1,
  R2 ↦ᵣ RVal_Bits r2 ∗
  R3 ↦ᵣ RVal_Bits r3 ∗
  instr_pre (pc + 4) (
    R1 ↦ᵣ RVal_Bits (bv_sub r2 r3) ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    R3 ↦ᵣ RVal_Bits r3 ∗
    True
  ).
Global Instance : LithiumUnfold (@sub_R_R_R_spec) := I.

(* TODO: generalize *)
Definition csel_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  R1 ↦ᵣ RVal_Bits v1 ∗
  R2 ↦ᵣ RVal_Bits v2 ∗
  instr_pre (pc + 4) (
    R1 ↦ᵣ RVal_Bits (ite (bool_decide (bv_unsigned pstatez = 0)) v1 v2) ∗
    R2 ↦ᵣ RVal_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
    True
  ).
Global Instance : LithiumUnfold (@csel_spec) := I.
Ltac csel_spec_tac :=
  try bv_solve;
  rewrite bool_decide_true //;
  match goal with | |- bv_unsigned ?b = 0 => by destruct b using bv_1_ind end.

(* TODO: generalize *)
Definition csinc_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  R1 ↦ᵣ RVal_Bits v1 ∗
  R2 ↦ᵣ RVal_Bits v2 ∗
  instr_pre 0x000000001030004c (
    R1 ↦ᵣ RVal_Bits (ite (bool_decide (bv_unsigned pstatez = 1)) v1 (bv_add_Z v2 1)) ∗
    R2 ↦ᵣ RVal_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
    True
  ).
Global Instance : LithiumUnfold (@csinc_spec) := I.
Ltac csinc_spec_tac :=
  try bv_solve;
  rewrite bool_decide_false //=;
  match goal with | |- bv_unsigned ?b ≠ _ => by destruct b using bv_1_ind end.

Definition stp_uninit_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (Rbase : string) (offset : Z) (incr : bool) : iProp Σ :=
  ∃ (r1 r2 rbase : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  Rbase ↦ᵣ RVal_Bits rbase ∗
  (bv_add_Z rbase offset) ↦ₘ? 16 ∗
  ⌜0 < bv_unsigned rbase + offset ∧ bv_unsigned rbase + offset + 16 < 2 ^ 52⌝ ∗
  instr_pre (pc + 4) (
  reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    Rbase ↦ᵣ RVal_Bits (if incr then bv_add_Z rbase offset else rbase) ∗
    (bv_add_Z rbase offset) ↦ₘ r1 ∗
    (bv_add_Z rbase (offset + 8)) ↦ₘ r2 ∗
    True
  ).
Global Instance : LithiumUnfold (@stp_uninit_spec) := I.

Definition ldp_mapsto_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (Rbase : string) (offset : Z) (incr : option Z) : iProp Σ :=
  ∃ (r1 r2 rbase : bv 64),
  reg_col sys_regs ∗
  reg_col [(KindReg R1, UnknownShape); (KindReg R2, UnknownShape)] ∗
  Rbase ↦ᵣ RVal_Bits rbase ∗
  (bv_add_Z rbase offset) ↦ₘ r1 ∗
  (bv_add_Z rbase (offset + 8)) ↦ₘ r2 ∗
  ⌜0 < bv_unsigned rbase + offset ∧ bv_unsigned rbase + offset + 16 < 2 ^ 52⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    Rbase ↦ᵣ RVal_Bits (if incr is Some i then bv_add_Z rbase i else rbase) ∗
    (bv_add_Z rbase offset) ↦ₘ r1 ∗
    (bv_add_Z rbase (offset + 8)) ↦ₘ r2 ∗
    True
  ).
Global Instance : LithiumUnfold (@ldp_mapsto_spec) := I.
