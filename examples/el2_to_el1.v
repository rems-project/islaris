Require Import isla.aarch64.aarch64.
From isla.instructions.el2_to_el1 Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*
Layout of SPSR_EL2:
0    0    0    0    0    3    C    4
0000 0000 0000 0000 0000 0011 1100 0100
0    |    |    |    |    |    |    |    N: saved PSTATE.N
 0   |    |    |    |    |    |    |    Z: saved PSTATE.Z
  0  |    |    |    |    |    |    |    C: saved PSTATE.C
   0 |    |    |    |    |    |    |    V: saved PSTATE.V
     00   |    |    |    |    |    |    reserved
       0  |    |    |    |    |    |    TCO: saved PSTATE.TCO
        0 |    |    |    |    |    |    DIT: saved PSTATE.DIT
          0    |    |    |    |    |    UAO: saved PSTATE.UAO
           0   |    |    |    |    |    PAN: saved PSTATE.PAN
            0  |    |    |    |    |    SS: saved PSTATE.SS
             0 |    |    |    |    |    IL: saved PSTATE.IL
               0000 000  |    |    |    reserved
                       0 |    |    |    SSBS: saved PSTATE.SSBS
                         00   |    |    BTYPE: saved PSTATE.BTYPE
                           1  |    |    D: saved PSTATE.D (Debug exception mask)
                            1 |    |    A: saved PSTATE.A (SError interupt mask)
                              1    |    I: saved PSTATE.I (IRQ interupt mask)
                               1   |    F: saved PSTATE.F (FIQ interupt mask)
                                0  |    reserved
                                 0 |    nRW: saved PSTATE.nRW (AArch64 execution state)
                                   0100 M
                                   01   saved PSTATE.EL
                                     0  unused
                                      0 saved PSTATE.SP
*)

(*
Actually accessed: C, N, V, Z, SS, IL, A, I, F, PAN.
Not accessed: SP, EL, nRW, D, BTYPE, SBSS, UAO, DIT, TCO.
Why for SP and EL?
*)

Definition pstate_of_spsr (v : bv 32) : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "SP"   , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 0  1 v))));
  (KindField "PSTATE" "EL"   , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 2  2 v))));
  (KindField "PSTATE" "nRW"  , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 4  1 v))));
  (KindField "PSTATE" "F"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 6  1 v))));
  (KindField "PSTATE" "I"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 7  1 v))));
  (KindField "PSTATE" "A"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 8  1 v))));
  (KindField "PSTATE" "D"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 9  1 v))));
  (KindField "PSTATE" "BTYPE", BitsShape 2); (*ExactShape (RVal_Bits (bv_to_bvn (bv_extract 10 2 v))));*)
  (KindField "PSTATE" "SBSS" , BitsShape 1); (*ExactShape (RVal_Bits (bv_to_bvn (bv_extract 12 1 v))));*)
  (KindField "PSTATE" "IL"   , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 20 1 v))));
  (KindField "PSTATE" "SS"   , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 21 1 v))));
  (KindField "PSTATE" "PAN"  , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 22 1 v))));
  (KindField "PSTATE" "UAO"  , BitsShape 1); (*ExactShape (RVal_Bits (bv_to_bvn (bv_extract 23 1 v))));*)
  (KindField "PSTATE" "DIT"  , BitsShape 1); (*ExactShape (RVal_Bits (bv_to_bvn (bv_extract 24 1 v))));*)
  (KindField "PSTATE" "TCO"  , BitsShape 1); (*ExactShape (RVal_Bits (bv_to_bvn (bv_extract 25 1 v))));*)
  (KindField "PSTATE" "V"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 28 1 v))));
  (KindField "PSTATE" "C"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 29 1 v))));
  (KindField "PSTATE" "Z"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 30 1 v))));
  (KindField "PSTATE" "N"    , ExactShape (RVal_Bits (bv_to_bvn (bv_extract 31 1 v))))
].

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

(*
  ("SP"   , RVal_Bits [BV{1} 1]);
  ("EL"   , RVal_Bits [BV{2} 2]);
  ("nRW"  , RVal_Bits [BV{1} 0]);
  ("F"    , RegVal_Poison);
  ("I"    , RegVal_Poison);
  ("A"    , RegVal_Poison);
  ("D"    , RVal_Bits [BV{1} 1]);
  ("BTYPE", RegVal_Poison);
  ("SSBS" , RegVal_Poison);
  ("IL"   , RegVal_Poison);
  ("SS"   , RegVal_Poison);
  ("PAN"  , RegVal_Poison);
  ("UAO"  , RegVal_Poison);
  ("DIT"  , RegVal_Poison);
  ("TCO"  , RegVal_Poison);
  ("V"    , RVal_Bits [BV{1} 0]);
  ("C"    , RVal_Bits [BV{1} 0]);
  ("Z"    , RVal_Bits [BV{1} 0]);
  ("N"    , RVal_Bits [BV{1} 0]);

  (* The following are AArch32-only fields. *)
  ("GE"   , RegVal_Poison);
  ("Q"    , RegVal_Poison);
  ("E"    , RegVal_Poison);
  ("M"    , RegVal_Poison);
  ("IT"   , RegVal_Poison);
  ("T"    , RegVal_Poison);
  ("J"    , RegVal_Poison);
*)

Definition el2_to_el1_sys_regs :=
  let regs32 :=
    [ "CPTR_EL2" ; "CPTR_EL3" ; "CPACR_EL1" ; "CNTHCTL_EL2" ; "MDCR_EL2"
    ; "MDCR_EL3" ; "ICC_SRE_EL2" ; "ICC_SRE_EL3" ; "CNTKCTL_EL1"
    ; "ICH_HCR_EL2" ; "ICC_SRE_EL1_NS" ; "PMUSERENR_EL0" ; "MPAMHCR_EL2"
    ; "HSTR_EL2" ]
  in
  let regs64 :=
    [ "MPAM2_EL2" ; "MPAMIDR_EL1" ; "MPAM3_EL3" ; "MPIDR_EL1" ; "EventRegister" ]
  in
  let with_value :=
    [ ("CFG_ID_AA64PFR0_EL1_EL0", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL1", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL2", RVal_Bits [BV{4} 1])
    ; ("CFG_ID_AA64PFR0_EL1_EL3", RVal_Bits [BV{4} 1])
    ; ("OSLSR_EL1", RVal_Bits [BV{32} 0])
    ; ("EDSCR"    , RVal_Bits [BV{32} 0])
    ; ("MDSCR_EL1", RVal_Bits [BV{32} 0])
    ; ("HCR_EL2"  , RVal_Bits [BV{64} 0x0000000080000000])
    ; ("SCR_EL3"  , RVal_Bits [BV{32} 0x00000401])
    ; ("SCTLR_EL1", RVal_Bits [BV{64} 0x0000000004000002])
    ; ("SCTLR_EL2", RVal_Bits [BV{64} 0x0000000004000002])
    ; ("TCR_EL1", RVal_Bits [BV{64} 0]) ]
  in
  ((λ r, (KindReg r, BitsShape 32)) <$> regs32) ++
  ((λ r, (KindReg r, BitsShape 64)) <$> regs64) ++
  ((λ '(r, v), (KindReg r, ExactShape v)) <$> with_value).

Definition el2_to_el1_spec (v0 v1 : bv 64) (spsr : bv 32) : iProp Σ := (
  "R0" ↦ᵣ RVal_Bits v0 ∗
  "ELR_EL2" ↦ᵣ RVal_Bits v1 ∗
  "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
  reg_col initial_pstate ∗
  reg_col el2_to_el1_sys_regs ∗
  instr_pre 0x100000 (
    "R0" ↦ᵣ RVal_Bits [BV{64} 0x100000] ∗
    "ELR_EL2" ↦ᵣ RVal_Bits [BV{64} 0x100000] ∗
    "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
    reg_col (pstate_of_spsr spsr) ∗
    True
  )
)%I.
Global Instance : LithiumUnfold (el2_to_el1_spec) := I.

Lemma el2_to_el1 v0 v1 spsr :
  bv_extract 1  1 spsr = [BV{1} 0] → (* SPSR_EL2.M[1] is reserved: must be 0. *)
  bv_extract 2  2 spsr = [BV{2} 1] → (* SPSR_EL2.M[3:2] contains 1 (for EL1). *)
  bv_extract 4  1 spsr = [BV{1} 0] → (* SPSR_EL2.M[4] fixed to AArch64. *)
  bv_extract 20 1 spsr = [BV{1} 0] → (* SPSR_EL2.IL *)
  bv_extract 21 1 spsr = [BV{1} 0] → (* SPSR_EL2.SS *)
  instr 0x0000000000080000 (Some a80000) -∗
  instr 0x0000000000080004 (Some a80004) -∗
  instr 0x0000000000080008 (Some a80008) -∗
  instr_body 0x0000000000080000 (el2_to_el1_spec v0 v1 spsr).
Proof.
  move => *.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

End proof.
