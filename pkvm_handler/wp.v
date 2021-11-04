Require Import isla.aarch64.aarch64.
Require Import isla.examples.pkvm_handler.instrs.

Definition instrs_iprop `{!islaG Σ} `{!threadG} := ([∗ list] i ∈ instr_map, instr i.1 (Some i.2))%I.

Definition spec_stp `{!islaG Σ} `{!threadG} a sp : iProp Σ :=
    ∃ (vold1 vold2 v v': bv 64),
    "R0" ↦ᵣ RVal_Bits v ∗
    "R1" ↦ᵣ RVal_Bits v' ∗
    (bv_unsigned sp - 16) ↦ₘ vold1 ∗
    (bv_unsigned sp - 8) ↦ₘ vold2 ∗
    ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
    ⌜bv_unsigned sp > 16⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    "SP_EL2" ↦ᵣ RVal_Bits sp ∗
    reg_col sys_regs ∗
    instr_pre a (
      "R0" ↦ᵣ RVal_Bits v ∗
      "R1" ↦ᵣ RVal_Bits v' ∗
      "SP_EL2" ↦ᵣ RVal_Bits (bv_sub sp [BV{64} 16])∗
      reg_col sys_regs ∗
      (bv_unsigned sp - 16) ↦ₘ v ∗
      (bv_unsigned sp - 8) ↦ₘ v' ∗
      True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp : bv 64) :
  instr 0x7400 (Some a7400) -∗
  instr_body 0x7400 (spec_stp 0x7404 sp).
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

Definition mrs_regs :=
  mrs_regs_32 ++ mrs_regs_64.

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

Definition spec `{!islaG Σ} `{!threadG} (sp forward_smc_addr: bv 64) (esr : bv 32) : iProp Σ :=
  ∃ v0 v1 v5 v6: bv 64,
  reg_col sys_regs ∗
  reg_col mrs_regs ∗
  reg_col CNVZ_regs ∗
  (* Move to sys_regs *)
  "InGuardedPage" ↦ᵣ RVal_Bool false ∗
  "ESR_EL2" ↦ᵣ RVal_Bits esr ∗
  "R0" ↦ᵣ RVal_Bits v0 ∗
  "R1" ↦ᵣ RVal_Bits v1 ∗
  "R5" ↦ᵣ RVal_Bits v5 ∗
  "R6" ↦ᵣ RVal_Bits v6 ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  (bv_unsigned sp - 16) ↦ₘ? 8 ∗
  (bv_unsigned sp - 8) ↦ₘ? 8 ∗
  ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
  ⌜bv_unsigned sp > 16⌝ ∗
  ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
  0x77f8 ↦ₘ forward_smc_addr ∗
  (instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 ≠ 22⌝ ∗ ∃ (v : bv 64), "R0" ↦ᵣ RVal_Bits v ∗ ⌜bv_unsigned v ≠ 22⌝ ∗ True) ∧
  instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 = 22⌝ ∗ ⌜Z.ge (bv_unsigned v0) 3⌝ ∗ True)) ∗
  (* Possibly should handle that this address gets shifted (even if it's by zero in this code) *)
  instr_pre (bv_unsigned forward_smc_addr) (
    ⌜Z.shiftr (bv_unsigned esr) 26 = 22⌝ ∗
    ⌜Z.lt (bv_unsigned v0) 3⌝ ∗
    "SP_EL2" ↦ᵣ RVal_Bits sp ∗
    "R5" ↦ᵣ RVal_Bits forward_smc_addr ∗
    "R6" ↦ᵣ RVal_Bits [BV{64} 0] ∗
    True).

Lemma wp `{!islaG Σ} `{!threadG} sp esr forward_smc_addr:
  instr 29696 (Some a7400) ∗
  instr 29700 (Some a7404) ∗
  instr 29704 (Some a7408) ∗
  instr 29708 (Some a740c) ∗
  instr 29712 (Some a7410) ∗
  instr 29716 (Some a7414) ∗
  instr 29720 (Some a7418) ∗
  instr 29724 (Some a741c) ∗
  instr 29728 (Some a7420) ∗
  instr 29732 (Some a7424) ∗
  instr 29736 (Some a7428) ∗
  instr 29740 (Some a742c) ∗
  instr 29744 (Some a7430) ∗
  instr 29748 (Some a7434) ∗
  instr 29752 (Some a7438) ∗
  instr 29756 (Some a743c) -∗
  instr_body 0x7400 (spec sp forward_smc_addr esr).
Proof.
  unfold spec.
  iStartProof.
  repeat liAStep; liShow.
  + iDestruct select (_ ∧ _)%I as "[? _]".
    repeat liAStep; liShow.
  + iDestruct select (_ ∧ _)%I as "[_ ?]".
    repeat liAStep; liShow.
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  * rewrite <- H4.
    assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    by rewrite G in H3.
  * contradict H4.
    rewrite H3.
    rewrite <- H4.
    by bits_simplify.
  * rewrite <- H4.
    assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    by rewrite G in H3.
Qed.
