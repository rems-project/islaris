Require Import isla.aarch64.aarch64.
From isla.instructions.simple_hvc Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

Definition initial_pstate : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "SP"   , ExactShape (RVal_Bits [BV{1} 1]));
  (KindField "PSTATE" "EL"   , ExactShape (RVal_Bits [BV{2} 2]));
  (KindField "PSTATE" "nRW"  , ExactShape (RVal_Bits [BV{1} 0]));
  (KindField "PSTATE" "F"    , BitsShape 1);
  (KindField "PSTATE" "I"    , BitsShape 1);
  (KindField "PSTATE" "A"    , BitsShape 1);
  (KindField "PSTATE" "D"    , ExactShape (RVal_Bits [BV{1} 1]));
  (KindField "PSTATE" "BTYPE", BitsShape 2);
  (KindField "PSTATE" "SBSS" , BitsShape 1);
  (KindField "PSTATE" "IL"   , BitsShape 1);
  (KindField "PSTATE" "SS"   , BitsShape 1);
  (KindField "PSTATE" "PAN"  , BitsShape 1);
  (KindField "PSTATE" "UAO"  , BitsShape 1);
  (KindField "PSTATE" "DIT"  , BitsShape 1);
  (KindField "PSTATE" "TCO"  , BitsShape 1);
  (KindField "PSTATE" "V"    , BitsShape 1);
  (KindField "PSTATE" "C"    , BitsShape 1);
  (KindField "PSTATE" "Z"    , BitsShape 1);
  (KindField "PSTATE" "N"    , BitsShape 1)
].

Definition simple_hvc_fixed_sys_regs :=
  let regs32 :=
    [ "CPTR_EL2" ; "CPTR_EL3" ; "CPACR_EL1" ; "CNTHCTL_EL2"
    ; "ICC_SRE_EL2" ; "ICC_SRE_EL3" ; "CNTKCTL_EL1"
    ; "ICH_HCR_EL2" ; "ICC_SRE_EL1_NS" ; "PMUSERENR_EL0" ; "MPAMHCR_EL2"
    ; "HSTR_EL2" ; "ESR_EL2" ; "ESR_EL1" ]
  in
  let regs64 :=
    [ "MPAM2_EL2" ; "MPAMIDR_EL1" ; "MPAM3_EL3" ; "MPIDR_EL1"
    ; "FAR_EL2" ; "HPFAR_EL2" ; "VBAR_EL1" ; "FAR_EL1"
    ; "SPSR_EL1" ; "ELR_EL1" ]
  in
  let with_value :=
    [ ("CFG_ID_AA64PFR0_EL1_EL0", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL1", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL2", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL3", RVal_Bits [BV{4} 1])
    ; ("OSLSR_EL1", RVal_Bits [BV{32} 0])
    ; ("EDSCR"    , RVal_Bits [BV{32} 0])
    ; ("MDSCR_EL1", RVal_Bits [BV{32} 0])
    ; ("MDCR_EL2" , RVal_Bits [BV{32} 0])
    ; ("MDCR_EL3" , RVal_Bits [BV{32} 0])
    ; ("SCR_EL3"  , RVal_Bits [BV{32} 0x00000501])
    ; ("SCTLR_EL1", RVal_Bits [BV{64} 0x0000000004000002])
    ; ("SCTLR_EL2", RVal_Bits [BV{64} 0x0000000004000002])
    ; ("TCR_EL1", RVal_Bits [BV{64} 0])
    ; ("TCR_EL2", RVal_Bits [BV{64} 0]) ]
  in
  ((λ r, (KindReg r, BitsShape 32)) <$> regs32) ++
  ((λ r, (KindReg r, BitsShape 64)) <$> regs64) ++
  ((λ '(r, v), (KindReg r, ExactShape v)) <$> with_value) ++
  [ (KindReg "EventRegister", BitsShape 1) ].

Definition simple_hvc_spec (v0 v1 : bv 64) (v2 : bv 32) : iProp Σ := (
  "R0"       ↦ᵣ RVal_Bits v0 ∗
  "VBAR_EL2" ↦ᵣ RVal_Bits [BV{64} 0x0] ∗
  "HCR_EL2"  ↦ᵣ RVal_Bits [BV{64} 0x80000000] ∗
  "ELR_EL2"  ↦ᵣ RVal_Bits v1 ∗
  "SPSR_EL2" ↦ᵣ RVal_Bits v2 ∗
  reg_col initial_pstate ∗
  reg_col simple_hvc_fixed_sys_regs ∗
  instr_pre 0x90008 (
    "R0" ↦ᵣ RVal_Bits [BV{64} 42] ∗
    "VBAR_EL2" ↦ᵣ RVal_Bits [BV{64} 0xa0000] ∗
    "HCR_EL2"  ↦ᵣ RVal_Bits [BV{64} 0x80000000] ∗
    "ELR_EL2"  ↦ᵣ RVal_Bits [BV{64} 0x90008] ∗
    (* FIXME "SPSR_EL2" ↦ᵣ RVal_Bits [BV{32} 0x3c4] ∗ *)
    (* FIXME reg_col initial_pstate ∗ *)
    reg_col simple_hvc_fixed_sys_regs ∗
    True
  )
)%I.
Global Instance : LithiumUnfold (simple_hvc_spec) := I.

Lemma simple_hvc v0 v1 v2 :
  ([∗ list] c ∈ instr_map, instr c.1 (Some c.2))%I -∗
  instr_body 0x0000000000080000 (simple_hvc_spec v0 v1 v2).
Proof.
  move => * /=.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

End proof.
