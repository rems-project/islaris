Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.examples.sys_regs.
From isla.instructions.binary_search Require Import instrs.

Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"].
Definition tmp_registers : list string :=
  ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"].


Definition c_call `{!islaG Σ} `{!threadG} (args : list (bv 64)) (P : iProp Σ) (Q : list (bv 64) → iProp Σ) : iProp Σ :=
  ∃ (ret : bv 64),
  ∃ (sp r8 r19 r20 r21 r22 r23 r24 r25 r26 r27 r28 r29 : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (RegColDirect r, None)) <$> tmp_registers) ∗
  ([∗ list] r;a∈args_registers;args, r ↦ᵣ Val_Bits (a : bv 64)) ∗
  "R8" ↦ᵣ Val_Bits r8 ∗
  "R19" ↦ᵣ Val_Bits r19 ∗
  "R20" ↦ᵣ Val_Bits r20 ∗
  "R21" ↦ᵣ Val_Bits r21 ∗
  "R22" ↦ᵣ Val_Bits r22 ∗
  "R23" ↦ᵣ Val_Bits r23 ∗
  "R24" ↦ᵣ Val_Bits r24 ∗
  "R25" ↦ᵣ Val_Bits r25 ∗
  "R26" ↦ᵣ Val_Bits r26 ∗
  "R27" ↦ᵣ Val_Bits r27 ∗
  "R28" ↦ᵣ Val_Bits r28 ∗
  "R29" ↦ᵣ Val_Bits r29 ∗
  "R30" ↦ᵣ Val_Bits ret ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  P ∗
  instr_pre (bv_unsigned ret) (
    ∃ (r0 r1 r2 r3 r4 r5 r6 r7 r8 : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ Val_Bits r0 ∗
      "R1" ↦ᵣ Val_Bits r1 ∗
      "R2" ↦ᵣ Val_Bits r2 ∗
      "R3" ↦ᵣ Val_Bits r3 ∗
      "R4" ↦ᵣ Val_Bits r4 ∗
      "R5" ↦ᵣ Val_Bits r5 ∗
      "R6" ↦ᵣ Val_Bits r6 ∗
      "R7" ↦ᵣ Val_Bits r7 ∗
      "R8" ↦ᵣ Val_Bits r8 ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> tmp_registers) ∗
      "R19" ↦ᵣ Val_Bits r19 ∗
      "R20" ↦ᵣ Val_Bits r20 ∗
      "R21" ↦ᵣ Val_Bits r21 ∗
      "R22" ↦ᵣ Val_Bits r22 ∗
      "R23" ↦ᵣ Val_Bits r23 ∗
      "R24" ↦ᵣ Val_Bits r24 ∗
      "R25" ↦ᵣ Val_Bits r25 ∗
      "R26" ↦ᵣ Val_Bits r26 ∗
      "R27" ↦ᵣ Val_Bits r27 ∗
      "R28" ↦ᵣ Val_Bits r28 ∗
      "R29" ↦ᵣ Val_Bits r29 ∗
      "R30" ↦ᵣ Val_Bits ret ∗
      "SP_EL2" ↦ᵣ Val_Bits sp ∗
      Q [r0; r1; r2; r3; r4; r5; r6; r7; r8] ∗
      True
  ).

Arguments c_call _ _ _ /.

Definition comp_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ r0 r1 r2 r3 r4 r5 r6 r7,
  c_call [r0; r1; r2; r3; r4; r5; r6; r7] True (λ rets, True).


Definition binary_search_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (x l r comp xs tmp2 tmp5 : bv 64) (data : list (bv 64)),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17" ]) ∗
  "R19" ↦ᵣ Val_Bits x ∗
  "R20" ↦ᵣ Val_Bits r ∗
  "R21" ↦ᵣ Val_Bits xs ∗
  "R22" ↦ᵣ Val_Bits comp ∗
  "R23" ↦ᵣ Val_Bits l ∗
  "R24" ↦ᵣ Val_Bits tmp2 ∗
  "R30" ↦ᵣ Val_Bits tmp5 ∗
  xs ↦ₘ∗ data ∗
  ⌜bv_unsigned l < bv_unsigned r ≤ length data⌝ ∗
  ⌜bv_unsigned xs + (length data) * 8 < 2 ^ 52⌝ ∗
  □ instr_pre (bv_unsigned comp) comp_spec ∗
  instr_pre 0x0000000010300054 (
    ∃ (tmp2 tmp5 : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17" ]) ∗
      "R19" ↦ᵣ Val_Bits x ∗
      "R20" ↦ᵣ Val_Bits r ∗
      "R21" ↦ᵣ Val_Bits xs ∗
      "R22" ↦ᵣ Val_Bits comp ∗
      "R23" ↦ᵣ Val_Bits l ∗
      "R24" ↦ᵣ Val_Bits tmp2 ∗
      "R30" ↦ᵣ Val_Bits tmp5 ∗
      xs ↦ₘ∗ data ∗
      True
  )
.

Arguments binary_search_loop_spec /.

Lemma binary_search_loop `{!islaG Σ} `{!threadG} :
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗
  instr 0x000000001030003c (Some a3c) -∗
  instr 0x0000000010300040 (Some a40) -∗
  instr 0x0000000010300044 (Some a44) -∗
  instr 0x0000000010300048 (Some a48) -∗
  instr 0x000000001030004c (Some a4c) -∗
  instr 0x0000000010300050 (Some a50) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x000000001030002c binary_search_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2)).
  Time repeat liAStep; liShow.
  iEval (rewrite /comp_spec /=).
  Time repeat liAStep; liShow.

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
