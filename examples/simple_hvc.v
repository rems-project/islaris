(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import isla.aarch64.aarch64.
From isla.instructions.simple_hvc Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*SPEC_START*)
Definition initial_pstate : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "SP"   , ExactShape (RVal_Bits (BV 1 1)));
  (KindField "PSTATE" "EL"   , ExactShape (RVal_Bits (BV 2 2)));
  (KindField "PSTATE" "nRW"  , ExactShape (RVal_Bits (BV 1 0)));
  (KindField "PSTATE" "F"    , BitsShape 1);
  (KindField "PSTATE" "I"    , BitsShape 1);
  (KindField "PSTATE" "A"    , BitsShape 1);
  (KindField "PSTATE" "D"    , ExactShape (RVal_Bits (BV 1 1)));
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

Definition final_pstate : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "SP"   , ExactShape (RVal_Bits (BV 1 0)));
  (KindField "PSTATE" "EL"   , ExactShape (RVal_Bits (BV 2 1)));
  (KindField "PSTATE" "nRW"  , ExactShape (RVal_Bits (BV 1 0)));
  (KindField "PSTATE" "F"    , BitsShape 1);
  (KindField "PSTATE" "I"    , BitsShape 1);
  (KindField "PSTATE" "A"    , BitsShape 1);
  (KindField "PSTATE" "D"    , ExactShape (RVal_Bits (BV 1 1)));
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
    [ ("CFG_ID_AA64PFR0_EL1_EL0", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL1", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL2", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL3", RVal_Bits (BV 4 1))
    ; ("OSLSR_EL1", RVal_Bits (BV 32 0))
    ; ("EDSCR"    , RVal_Bits (BV 32 0))
    ; ("MDSCR_EL1", RVal_Bits (BV 32 0))
    ; ("MDCR_EL2" , RVal_Bits (BV 32 0))
    ; ("MDCR_EL3" , RVal_Bits (BV 32 0))
    ; ("SCR_EL3"  , RVal_Bits (BV 32 0x00000501))
    ; ("SCTLR_EL1", RVal_Bits (BV 64 0x0000000004000002))
    ; ("SCTLR_EL2", RVal_Bits (BV 64 0x0000000004000002))
    ; ("TCR_EL1", RVal_Bits (BV 64 0))
    ; ("TCR_EL2", RVal_Bits (BV 64 0)) ]
  in
  ((λ r, (KindReg r, BitsShape 32)) <$> regs32) ++
  ((λ r, (KindReg r, BitsShape 64)) <$> regs64) ++
  ((λ '(r, v), (KindReg r, ExactShape v)) <$> with_value) ++
  [ (KindReg "EventRegister", BitsShape 1) ].

Definition simple_hvc_spec (v0 v1 : bv 64) (v2 : bv 32) : iProp Σ := (
  "R0"       ↦ᵣ RVal_Bits v0 ∗
  "VBAR_EL2" ↦ᵣ RVal_Bits (BV 64 0x0) ∗
  "HCR_EL2"  ↦ᵣ RVal_Bits (BV 64 0x80000000) ∗
  "ELR_EL2"  ↦ᵣ RVal_Bits v1 ∗
  "SPSR_EL2" ↦ᵣ RVal_Bits v2 ∗
  reg_col initial_pstate ∗
  reg_col simple_hvc_fixed_sys_regs ∗
  instr_pre 0x90008 (
    "R0" ↦ᵣ RVal_Bits (BV 64 42) ∗
    "VBAR_EL2" ↦ᵣ RVal_Bits (BV 64 0xa0000) ∗
    "HCR_EL2"  ↦ᵣ RVal_Bits (BV 64 0x80000000) ∗
    "ELR_EL2"  ↦ᵣ RVal_Bits (BV 64 0x90008) ∗
    "SPSR_EL2" ↦ᵣ RVal_Bits (BV 32 0x3c4) ∗
    reg_col final_pstate ∗
    reg_col simple_hvc_fixed_sys_regs ∗
    True
  )
)%I.
(*SPEC_END*)
Global Instance : LithiumUnfold (simple_hvc_spec) := I.

Lemma simple_hvc v0 v1 v2 :
  ([∗ list] c ∈ instr_map, instr c.1 (Some c.2))%I -∗
  instr_body 0x0000000000080000 (simple_hvc_spec v0 v1 v2).
Proof.
(*PROOF_START*)
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
(*PROOF_END*)
Time Qed.

End proof.
