Require Import isla.aarch64.aarch64.
Require Import isla.examples.pkvm_handler.instrs.

Definition instrs_iprop `{!islaG Σ} `{!threadG} := ([∗ list] i ∈ instr_map, instr i.1 (Some i.2))%I.

Definition spec_stp `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
    ∃ (vold1 vold2 : bv 64),
    "R0" ↦ᵣ RVal_Bits v1 ∗
    "R1" ↦ᵣ RVal_Bits v2 ∗
    (bv_sub sp [BV{64} 16]) ↦ₘ vold1 ∗
    (bv_sub sp [BV{64} 8]) ↦ₘ vold2 ∗
    ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
    ⌜bv_unsigned sp > 16⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    "SP_EL2" ↦ᵣ RVal_Bits sp ∗
    reg_col sys_regs ∗
    instr_pre a (
      "R0" ↦ᵣ RVal_Bits v1 ∗
      "R1" ↦ᵣ RVal_Bits v2 ∗
      "SP_EL2" ↦ᵣ RVal_Bits (bv_sub sp [BV{64} 16])∗
      reg_col sys_regs ∗
      (bv_sub sp [BV{64} 16]) ↦ₘ v1 ∗
      (bv_sub sp [BV{64} 8]) ↦ₘ v2 ∗
      True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64) :
  instr 0x7400 (Some a7400) -∗
  instr_body 0x7400 (spec_stp 0x7404 sp v1 v2).
Proof.
  iStartProof.
  unfold spec_stp.
  unfold instrs_iprop.
  simpl.
  repeat liAStep; liShow.
  Unshelve.
  all: try (repeat f_equal; bv_solve).
  all: prepare_sidecond; bv_solve.
Qed.

Definition mrs_regs_32 :=
  (λ r, (KindReg r, BitsShape 64)) <$>
  ["CPTR_EL2"; "CPTR_EL3"; "CPACR_EL1";
  "CNTHCTL_EL2"; "MDCR_EL2"; "ICC_SRE_EL2";
  "CNTKCTL_EL1"; "MDCR_EL3";
  "ICH_HCR_EL2"; "ICC_SRE_EL1_NS";
  "PMUSERENR_EL0"; "ICC_SRE_EL3";
  "MPAMHCR_EL2"; "HSTR_EL2"].

Definition mrs_regs_64 :=
  (λ r, (KindReg r, BitsShape 64)) <$>
  ["MPAM2_EL2"; "MPAMIDR_EL1"; "MPAM3_EL3"].


Definition exists_reg r :=
  [(KindReg r, BitsShape 64)].

Definition spec_mrs `{!islaG Σ} `{!threadG} a (vold : bv 32) (v : bv 64) x : iProp Σ :=
  reg_col mrs_regs_32 ∗
  reg_col mrs_regs_64 ∗
  reg_col (exists_reg "R0") ∗
  reg_col sys_regs ∗
  "ESR_EL2" ↦ᵣ RVal_Bits vold ∗
  ⌜bv_unsigned vold = x⌝ ∗
  ⌜bv_unsigned v = x⌝ ∗
  instr_pre a (
    reg_col sys_regs ∗
    "R0" ↦ᵣ RVal_Bits v ∗
    True
  ).

Lemma mrs_wp `{!islaG Σ} `{!threadG} (vold: bv 32) (v : bv 64) x :
  instr 0x7404 (Some a7404) -∗
  instr_body 0x7404 (spec_mrs 0x7408 vold v x).
Proof.
  iStartProof.
  unfold spec_mrs.
  unfold exists_reg.
  repeat liAStep; liShow.
  Unshelve.
  (* TODO: Check if bv_solve on the latest branch solves this, otherwise fix it *)
  all: prepare_sidecond.
  bv_solve.
Qed.

Definition spec_lsr `{!islaG Σ} `{!threadG} a (v vold : bv 64) : iProp Σ :=
  "R0" ↦ᵣ RVal_Bits vold ∗
  ⌜bv_unsigned v = Z.shiftr (bv_unsigned vold) 26⌝ ∗
  reg_col sys_regs ∗
  instr_pre a (
    reg_col sys_regs ∗
    "R0" ↦ᵣ RVal_Bits v ∗
    True
  ).


Lemma lsr_wp `{!islaG Σ} `{!threadG} (v vold : bv 64):
  instr 0x7408 (Some a7408) -∗
  instr_body 0x7408 (spec_lsr 0x740c v vold).
Proof.
  iStartProof.
  unfold spec_lsr.
  repeat liAStep; liShow.
  Unshelve.
  all: prepare_sidecond.
  by bits_simplify.
Qed.
