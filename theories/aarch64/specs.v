Require Import isla.automation.
Require Import isla.aarch64.arch.
Require Import isla.aarch64.sys_regs.

Definition sub_R_R_R_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 R3 : string) : iProp Σ :=
  ∃ (r2 r3 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ: λ r1,
  R2 ↦ᵣ RVal_Bits r2 ∗
  R3 ↦ᵣ RVal_Bits r3 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits (bv_sub r2 r3) ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    R3 ↦ᵣ RVal_Bits r3 ∗
    True
  ).
Global Instance : LithiumUnfold (@sub_R_R_R_spec) := I.

Definition sub_R_R_R_self_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits (bv_sub r1 r2) ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    True
  ).
Global Instance : LithiumUnfold (@sub_R_R_R_self_spec) := I.

Definition cmp_R_R_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits (bv_extract 63 1 (bv_sub r1 r2)) ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (r1 = r2))) ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_unsigned r2 ≤ bv_unsigned r1))) ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_signed (bv_sub r1 r2) ≠ bv_signed r1 - bv_signed r2))) ∗
    True
  ).
Global Instance : LithiumUnfold (@cmp_R_R_spec) := I.
Ltac cmp_spec_tac1 :=
  bv_simplify => /=; do 2 f_equal; bv_solve.
Ltac cmp_spec_tac2 :=
  let Hbv := fresh in let Heq := fresh in
  apply bv_eq; case_bool_decide as Hbv; case_bool_decide as Heq => //; subst; contradict Hbv;
    try move/bv_eq in Heq; bv_solve.
Ltac cmp_spec_tac3 :=
  let Hbv := fresh in
  apply bv_eq; case_bool_decide as Hbv; case_bool_decide => //; exfalso; contradict Hbv; bv_solve.
Ltac cmp_spec_tac4 :=
  let Hbv := fresh in let Heq := fresh in
  apply bv_eq;
  case_bool_decide as Hbv; case_bool_decide as Heq => //; exfalso; contradict Hbv;
    apply/bv_eq_signed; bv_simplify_arith;
    bv_simplify_arith_hyp Heq;
    bv_solve.

Definition cmp_R_imm_spec `{!islaG Σ} `{!threadG} (pc : Z) (R : string) (imm : Z) : iProp Σ :=
  ∃ (r1 : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  R ↦ᵣ RVal_Bits r1 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R ↦ᵣ RVal_Bits r1 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits (bv_extract 63 1 (bv_sub_Z r1 imm)) ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_unsigned r1 = imm))) ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (imm ≤ bv_unsigned r1))) ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_signed (bv_sub_Z r1 imm) ≠ bv_signed r1 - imm))) ∗
    True
  ).
Global Instance : LithiumUnfold (@cmp_R_imm_spec) := I.

(* TODO: generalize *)
Definition csel_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  reg_col sys_regs ∗
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  R1 ↦ᵣ RVal_Bits v1 ∗
  R2 ↦ᵣ RVal_Bits v2 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
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
  reg_col sys_regs ∗
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  R1 ↦ᵣ RVal_Bits v1 ∗
  R2 ↦ᵣ RVal_Bits v2 ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
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
  (bv_unsigned rbase + offset) ↦ₘ? 16 ∗
  ⌜bv_unsigned rbase `mod` 8 = 0⌝ ∗
  ⌜0 < bv_unsigned rbase + offset ∧ bv_unsigned rbase + offset + 16 < 2 ^ 52⌝ ∗
  instr_pre (pc + 4) (
  reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    Rbase ↦ᵣ RVal_Bits (if incr then bv_add_Z rbase offset else rbase) ∗
    (bv_unsigned rbase + offset) ↦ₘ r1 ∗
    (bv_unsigned rbase + offset + 8) ↦ₘ r2 ∗
    True
  ).
Global Instance : LithiumUnfold (@stp_uninit_spec) := I.

Definition ldp_mapsto_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 R2 : string) (Rbase : string) (offset : Z) (incr : option Z) : iProp Σ :=
  ∃ (r1 r2 rbase : bv 64),
  reg_col sys_regs ∗
  reg_col [(KindReg R1, UnknownShape); (KindReg R2, UnknownShape)] ∗
  Rbase ↦ᵣ RVal_Bits rbase ∗
  (bv_unsigned rbase + offset) ↦ₘ r1 ∗
  (bv_unsigned rbase + offset + 8) ↦ₘ r2 ∗
  ⌜bv_unsigned rbase `mod` 8 = 0⌝ ∗
  ⌜0 < bv_unsigned rbase + offset ∧ bv_unsigned rbase + offset + 16 < 2 ^ 52⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    Rbase ↦ᵣ RVal_Bits (if incr is Some i then bv_add_Z rbase i else rbase) ∗
    (bv_unsigned rbase + offset) ↦ₘ r1 ∗
    (bv_unsigned rbase + offset + 8) ↦ₘ r2 ∗
    True
  ).
Global Instance : LithiumUnfold (@ldp_mapsto_spec) := I.

Definition ldr_mapsto_spec `{!islaG Σ} `{!threadG} (pc : Z) (pcval : Z) (R1 : string) (addr : Z) : iProp Σ :=
  ∃ (r1 : bv 64),
  reg_col sys_regs ∗
  reg_col [(KindReg R1, UnknownShape)] ∗
  addr ↦ₘ r1 ∗
  ⌜pc = pcval⌝ ∗
  ⌜addr `mod` 8 = 0⌝ ∗
  ⌜0 < addr ∧ addr + 16 < 2 ^ 52⌝ ∗
  instr_pre (pc + 4) (
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits r1 ∗
    addr ↦ₘ r1 ∗
    True
  ).
Global Instance : LithiumUnfold (@ldr_mapsto_spec) := I.


(* Is there a nice way to write this that handles both the R to R and R to same R cases? *)
Definition lsr_R_spec `{!islaG Σ} `{!threadG} (pc : Z) (R1 : string) (shift : Z) : iProp Σ :=
  ∃ (v1 : bv 64),
  reg_col sys_regs ∗
  R1 ↦ᵣ RVal_Bits v1 ∗
  instr_pre (pc + 4) (
    ∃ vnew : bv 64,
    reg_col sys_regs ∗
    R1 ↦ᵣ RVal_Bits vnew ∗
    ⌜bv_unsigned vnew = Z.shiftr (bv_unsigned v1) shift⌝ ∗
    True
  ).
Global Instance : LithiumUnfold (@lsr_R_spec) := I.

Definition movk_spec `{!islaG Σ} `{!threadG} (pc : Z) (R : string) (start : Z) (result : Z) : iProp Σ :=
  ∃ (v : bv 64),
  reg_col sys_regs ∗
  R ↦ᵣ RVal_Bits v ∗
  ⌜bv_unsigned v = start⌝ ∗
  instr_pre (pc + 4) (
    ∃ (vresult : bv 64),
    reg_col sys_regs ∗
    R ↦ᵣ RVal_Bits vresult ∗
    ⌜bv_unsigned vresult = result⌝ ∗
    True
  ).
Global Instance : LithiumUnfold (@movk_spec) := I.
