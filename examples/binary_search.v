Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.examples.sys_regs.
From isla.instructions.binary_search Require Import instrs.

Global Instance valu_inhabited : Inhabited valu := populate (RegVal_Base (Val_Bool true)).
Definition bool_to_bv (n : N) (b : bool) : bv n :=
  Z_to_bv n (Z_of_bool b).

Lemma bv_extract_bool_to_bv n1 n2 b:
  bv_extract 0 n1 (bool_to_bv n2 b) = bool_to_bv n1 b.
Proof.
  apply bv_eq.
  rewrite bv_extract_unsigned.
Admitted.
Lemma bv_not_bool_to_bv b:
  bv_not (bool_to_bv 1 b) = bool_to_bv 1 (negb b).
Proof. apply bv_eq. by destruct b. Qed.


Section proof.
Context `{!islaG Σ} `{!threadG}.

Definition tmp_registers : list string :=
  ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"].

Definition c_call (P : list valu → ((list valu → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ (sp ret : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (RegColDirect r, None)) <$> tmp_registers) ∗
  "R0" ↦ᵣ: λ r0,
  "R1" ↦ᵣ: λ r1,
  "R2" ↦ᵣ: λ r2,
  "R3" ↦ᵣ: λ r3,
  "R4" ↦ᵣ: λ r4,
  "R5" ↦ᵣ: λ r5,
  "R6" ↦ᵣ: λ r6,
  "R7" ↦ᵣ: λ r7,
  "R8" ↦ᵣ: λ r8,
  "R19" ↦ᵣ: λ r19,
  "R20" ↦ᵣ: λ r20,
  "R21" ↦ᵣ: λ r21,
  "R22" ↦ᵣ: λ r22,
  "R23" ↦ᵣ: λ r23,
  "R24" ↦ᵣ: λ r24,
  "R25" ↦ᵣ: λ r25,
  "R26" ↦ᵣ: λ r26,
  "R27" ↦ᵣ: λ r27,
  "R28" ↦ᵣ: λ r28,
  "R29" ↦ᵣ: λ r29,
  "R30" ↦ᵣ Val_Bits ret ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  P [r0; r1; r2; r3; r4; r5; r6; r7] (λ Q,
  instr_pre (bv_unsigned ret) (
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"]) ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> tmp_registers) ∗
      "R0" ↦ᵣ: λ r0',
      "R1" ↦ᵣ: λ r1',
      "R2" ↦ᵣ: λ r2',
      "R3" ↦ᵣ: λ r3',
      "R4" ↦ᵣ: λ r4',
      "R5" ↦ᵣ: λ r5',
      "R6" ↦ᵣ: λ r6',
      "R7" ↦ᵣ: λ r7',
      "R8" ↦ᵣ: λ r8',
      "R19" ↦ᵣ r19 ∗
      "R20" ↦ᵣ r20 ∗
      "R21" ↦ᵣ r21 ∗
      "R22" ↦ᵣ r22 ∗
      "R23" ↦ᵣ r23 ∗
      "R24" ↦ᵣ r24 ∗
      "R25" ↦ᵣ r25 ∗
      "R26" ↦ᵣ r26 ∗
      "R27" ↦ᵣ r27 ∗
      "R28" ↦ᵣ r28 ∗
      "R29" ↦ᵣ r29 ∗
      "R30" ↦ᵣ Val_Bits ret ∗
      "SP_EL2" ↦ᵣ Val_Bits sp ∗
      Q [r0'; r1'; r2'; r3'; r4'; r5'; r6'; r7'; r8']
  )).
Hint Unfold c_call : isla_unfold.

Definition comp_spec : iProp Σ :=
  (c_call (λ args R, R (λ rets, ∃ b : bool, ⌜rets !!! 0%nat = RegVal_Base (Val_Bits (bool_to_bv 64 b))⌝)))%I.
Hint Unfold comp_spec : isla_unfold.

Definition a40_tst_imm_spec : iProp Σ :=
  ∃ (v : bv 64),
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ Val_Bits v ∗
  instr_pre 0x0000000010300044 (
    "R0" ↦ᵣ Val_Bits v ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits [BV{1} 0] ∗
    "PSTATE" # "Z" ↦ᵣ Val_Bits (bv_not (bv_extract 0 1 v)) ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits [BV{1} 0] ∗
    "PSTATE" # "V" ↦ᵣ Val_Bits [BV{1} 0] ∗
    True
  ).
Hint Unfold a40_tst_imm_spec : isla_unfold.

Lemma a40_has_tst_imm_spec :
  instr 0x0000000010300040 (Some a40) -∗
  instr_body 0x0000000010300040 (a40_tst_imm_spec).
Proof.
  iStartProof. rewrite /a40_tst_imm_spec.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - bv_simplify.
    rewrite Z.shiftr_eq_0 // ?Z.land_nonneg; [lia|].
    apply: Z.le_lt_trans; [apply Z.log2_land; bv_solve| bv_solve].
  - admit.
  - bv_simplify.
    rewrite Z.shiftr_eq_0 // ?Z.land_nonneg; [lia|].
    apply: Z.le_lt_trans; [apply Z.log2_land; bv_solve| bv_solve].
  - admit.
Admitted.

Definition a44_csel_spec : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
  "R20" ↦ᵣ Val_Bits v1 ∗
  "R24" ↦ᵣ Val_Bits v2 ∗
  instr_pre 0x0000000010300048 (
    "R20" ↦ᵣ Val_Bits (ite (bool_decide (bv_unsigned pstatez = 0)) v1 v2) ∗
    "R24" ↦ᵣ Val_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
    True
  ).
Hint Unfold a44_csel_spec : isla_unfold.

Lemma a44_has_csel_spec :
  instr 0x0000000010300044 (Some a44) -∗
  instr_body 0x0000000010300044 (a44_csel_spec).
Proof.
  iStartProof. rewrite /a44_csel_spec.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - rewrite bool_decide_true //.
    admit.
Admitted.

Definition a48_csinc_spec : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
  "R23" ↦ᵣ Val_Bits v1 ∗
  "R24" ↦ᵣ Val_Bits v2 ∗
  instr_pre 0x000000001030004c (
    "R23" ↦ᵣ Val_Bits (ite (bool_decide (bv_unsigned pstatez = 1)) v1 (bv_add_Z v2 1)) ∗
    "R24" ↦ᵣ Val_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
    True
  ).
Hint Unfold a48_csinc_spec : isla_unfold.

Lemma a48_has_csinc_spec :
  instr 0x0000000010300048 (Some a48) -∗
  instr_body 0x0000000010300048 (a48_csinc_spec).
Proof.
  iStartProof. rewrite /a48_csinc_spec.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - rewrite bool_decide_false //=.
    rename select (_ ≠ _) into Hz. contradict Hz. bv_solve.
Qed.


Definition binary_search_loop_spec : iProp Σ :=
  ∃ (x l r comp xs tmp2 sp : bv 64) (data : list (bv 64)),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R25"; "R26"; "R27"; "R28"; "R29"; "R30" ]) ∗
  "R19" ↦ᵣ Val_Bits x ∗
  "R20" ↦ᵣ Val_Bits r ∗
  "R21" ↦ᵣ Val_Bits xs ∗
  "R22" ↦ᵣ Val_Bits comp ∗
  "R23" ↦ᵣ Val_Bits l ∗
  "R24" ↦ᵣ Val_Bits tmp2 ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  xs ↦ₘ∗ data ∗
  ⌜bv_unsigned l < bv_unsigned r ≤ length data⌝ ∗
  ⌜bv_unsigned xs + (length data) * 8 < 2 ^ 52⌝ ∗
  □ instr_pre (bv_unsigned comp) comp_spec ∗
  instr_pre 0x0000000010300054 (
    ∃ (l' r' tmp2 : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R25"; "R26"; "R27"; "R28"; "R29"; "R30" ]) ∗
      "R19" ↦ᵣ Val_Bits x ∗
      "R20" ↦ᵣ Val_Bits r' ∗
      "R21" ↦ᵣ Val_Bits xs ∗
      "R22" ↦ᵣ Val_Bits comp ∗
      "R23" ↦ᵣ Val_Bits l' ∗
      "R24" ↦ᵣ Val_Bits tmp2 ∗
      "SP_EL2" ↦ᵣ Val_Bits sp ∗
      xs ↦ₘ∗ data ∗
      True
  )
.
Hint Unfold binary_search_loop_spec : isla_unfold.

Lemma binary_search_loop :
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗
  instr 0x000000001030003c (Some a3c) -∗
  (* instr 0x0000000010300040 (Some a40) -∗ *)
  instr_body 0x0000000010300040 (a40_tst_imm_spec) -∗
  (* instr 0x0000000010300044 (Some a44) -∗ *)
  instr_body 0x0000000010300044 (a44_csel_spec) -∗
  (* instr 0x0000000010300048 (Some a48) -∗ *)
  instr_body 0x0000000010300048 (a48_csinc_spec) -∗
  instr 0x000000001030004c (Some a4c) -∗
  instr 0x0000000010300050 (Some a50) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x000000001030002c binary_search_loop_spec.
Proof.
  iStartProof. rewrite {2}/binary_search_loop_spec.
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2)).
  Time repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  - bv_simplify.
    autorewrite with bv_unfolded_to_arith.
    have -> : (bv_wrap 64 (bv_unsigned l) + bv_wrap 64
                (bv_wrap 64
                   (bv_wrap 64 (bv_wrap 64 (bv_unsigned r) + bv_wrap 64 (bv_wrap 64 (- bv_unsigned l - 1))) + 1)
                   `div` 2 ^ 1))
             = (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2) by bv_solve.
    rewrite (bv_wrap_small 61 _); [|bv_solve].
    bv_solve.
  - bv_solve.
  - admit.
Abort.

Lemma binary_search `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗

  instr 0x0000000010300054 (Some a54) -∗
  instr 0x0000000010300058 (Some a58) -∗
  instr 0x000000001030005c (Some a5c) -∗
  instr 0x0000000010300060 (Some a60) -∗
  instr 0x0000000010300064 (Some a64) -∗
  instr 0x0000000010300068 (Some a68) -∗
  instr 0x000000001030006c (Some a6c) -∗
  instr 0x0000000010300070 (Some a70) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x0000000010300000 (
    ∃ (tmp1 tmp2 src dst n ret : bv 64) (srcdata dstdata : list byte),
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
    "R3" ↦ᵣ Val_Bits tmp2 ∗ "R4" ↦ᵣ Val_Bits tmp1 ∗
    "R30" ↦ᵣ Val_Bits ret ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp1 tmp2 n : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
      "R3" ↦ᵣ Val_Bits tmp2 ∗ "R4" ↦ᵣ Val_Bits tmp1 ∗
      "R30" ↦ᵣ Val_Bits ret ∗
      src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ srcdata ∗
      True
  )).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
Abort.
End proof.
