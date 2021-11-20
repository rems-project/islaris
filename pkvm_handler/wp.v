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
Require Import isla.examples.pkvm_handler.instrs.

(*SPEC_START*)
Definition pkvm_sys_regs' : list (reg_kind * valu_shape) := [
  (KindReg "SCTLR_EL1" , ExactShape (RVal_Bits [BV{64} 0x0000000004000002] ));
  (KindReg "SCR_EL3" , ExactShape (RVal_Bits [BV{32} 0x00000501] ));
  (KindReg "TCR_EL1" , ExactShape (RVal_Bits [BV{64} 0] ));
  (KindReg "TCR_EL2" , ExactShape (RVal_Bits [BV{64} 0] ));
  (KindReg "HCR_EL2" , ExactShape (RVal_Bits [BV{64} 0x0000000080000000] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL0" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL1" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL2" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "CFG_ID_AA64PFR0_EL1_EL3" , ExactShape (RVal_Bits [BV{4} 1] ));
  (KindReg "OSLSR_EL1" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "OSDLR_EL1" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "EDSCR" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "MPIDR_EL1" , ExactShape (RVal_Bits [BV{64} 0] ));
  (KindReg "MDSCR_EL1" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "MDCR_EL2" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindReg "MDCR_EL3" , ExactShape (RVal_Bits [BV{32} 0] ));
  (KindField "PSTATE" "SP" , ExactShape (RVal_Bits [BV{1} 1] ));
  (KindField "PSTATE" "nRW" , ExactShape (RVal_Bits [BV{1} 0] ));
  (KindField "PSTATE" "D" , ExactShape (RVal_Bits [BV{1} 1]));
  (KindReg "__isla_monomorphize_writes", ExactShape (RVal_Bool false));
  (KindReg "__isla_monomorphize_reads", ExactShape (RVal_Bool false));
  (KindReg "__highest_el_aarch32", ExactShape (RVal_Bool false));
  (KindReg "__CNTControlBase", ExactShape (RVal_Bits [BV{52} 0]));
  (KindReg "__v85_implemented", ExactShape (RVal_Bool false));
  (KindReg "__v84_implemented", ExactShape (RVal_Bool false));
  (KindReg "__v83_implemented", ExactShape (RVal_Bool false));
  (KindReg "__v82_implemented", ExactShape (RVal_Bool false));
  (KindReg "__v81_implemented", ExactShape (RVal_Bool true));
  (KindReg "__trickbox_enabled", ExactShape (RVal_Bool false))
].

Definition pkvm_sys_regs :=
  (KindReg "SCTLR_EL2", ExactShape (RVal_Bits [BV{64} 0x4000002])) ::
  (KindField "PSTATE" "EL" , ExactShape (RVal_Bits [BV{2} 2] )) ::
  pkvm_sys_regs'.
Definition pkvm_sys_regs_updated :=
  (KindReg "SCTLR_EL2", ExactShape (RVal_Bits [BV{64} 0x4000000])) ::
  (KindField "PSTATE" "EL" , ExactShape (RVal_Bits [BV{2} 2] )) ::
  pkvm_sys_regs'.
Definition pkvm_eret_sys_regs :=
  (KindReg "SCTLR_EL2", ExactShape (RVal_Bits [BV{64} 0x4000002])) ::
  (KindField "PSTATE" "EL" , ExactShape (RVal_Bits [BV{2} 1] )) ::
  pkvm_sys_regs'.
(*SPEC_END*)

Definition instrs_iprop `{!islaG Σ} `{!threadG} := ([∗ list] i ∈ instr_map, instr i.1 (Some i.2))%I.



(*SPEC_START*)
Definition mrs_regs_32 :=
  (λ r, (KindReg r, BitsShape 32)) <$>
  ["CPTR_EL2"; "CPTR_EL3"; "CPACR_EL1";
  "CNTHCTL_EL2"; "ICC_SRE_EL2";
  "CNTKCTL_EL1";
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

Definition rest_of_pstate : list (reg_kind * valu_shape) := [
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
  (KindField "PSTATE" "TCO"  , BitsShape 1)
].
(*SPEC_END*)

(*PROOF_START*)
Definition reset_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (elr : bv 64) (spsr : bv 32),
  reg_col pkvm_sys_regs ∗
  reg_col mrs_regs ∗
  reg_col CNVZ_regs ∗
  reg_col rest_of_pstate ∗
  reg_col [
    (KindReg "R5", BitsShape 64);
    (KindReg "R6", BitsShape 64);
    (KindReg "VBAR_EL2", BitsShape 64);
    (KindReg "EventRegister", BitsShape 1)
  ] ∗
  "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
  ⌜bv_extract 0  1 spsr = [BV{1} 1]⌝ ∗
  ⌜bv_extract 1  1 spsr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 2  2 spsr = [BV{2} 2]⌝ ∗
  ⌜bv_extract 4  1 spsr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 9  1 spsr = [BV{1} 1]⌝ ∗
  ⌜bv_extract 20 1 spsr = [BV{1} 0]⌝ ∗
  "ELR_EL2" ↦ᵣ RVal_Bits elr ∗
  ⌜bv_extract 55 1 elr = [BV{1} 0]⌝ ∗
  instr_body (bv_unsigned elr) (
    (* sctlr is updated by this code, but we claim to know enough about its value that the update is trivial.
       This should probably be relaxed
    *)
    reg_col pkvm_sys_regs_updated ∗
    reg_col mrs_regs ∗
    reg_col CNVZ_regs ∗
    reg_col rest_of_pstate ∗
    reg_col [
      (KindReg "R5", BitsShape 64);
      (KindReg "R6", BitsShape 64);
      (KindReg "SPSR_EL2", BitsShape 32);
      (KindReg "ELR_EL2", BitsShape 64);
      (KindReg "EventRegister", BitsShape 1)
    ] ∗
    "VBAR_EL2" ↦ᵣ RVal_Bits [BV{64} 116632] ∗
    True
  ).

  Definition stub_handler_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
    ∃ (b elr el2_cont: bv 64) (spsr : bv 32),
    reg_col pkvm_sys_regs ∗
    reg_col mrs_regs ∗
    reg_col CNVZ_regs ∗
    reg_col rest_of_pstate ∗
    reg_col [(KindReg "EventRegister", BitsShape 1)] ∗
    "R0" ↦ᵣ RVal_Bits b ∗
    "R1" ↦ᵣ RVal_Bits el2_cont ∗
    reg_col
      [
        (KindReg "R2", BitsShape 64);
        (KindReg "R3", BitsShape 64);
        (KindReg "R4", BitsShape 64);
        (KindReg "R5", BitsShape 64);
        (KindReg "R6", BitsShape 64);
        (KindReg "VBAR_EL2", BitsShape 64)
      ] ∗
    "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
    "ELR_EL2" ↦ᵣ RVal_Bits elr ∗
    ⌜bv_extract 0  1 spsr = [BV{1} 1]⌝ ∗
    ⌜bv_extract 1  1 spsr = [BV{1} 0]⌝ ∗
    ⌜bv_extract 2  2 spsr = [BV{2} 1]⌝ ∗
    ⌜bv_extract 4  1 spsr = [BV{1} 0]⌝ ∗
    ⌜bv_extract 9  1 spsr = [BV{1} 1]⌝ ∗
    ⌜bv_extract 20 1 spsr = [BV{1} 0]⌝ ∗
    ⌜bv_extract 55 1 elr = [BV{1} 0]⌝ ∗
    ⌜bv_extract 55 1 el2_cont = [BV{1} 0]⌝ ∗
    (* We handle only two of the 3 hypercalls this handler supports for now*)
    ⌜bv_unsigned b < 2⌝ ∗
    instr_body (bv_unsigned el2_cont) (
      (* There should be way more here, but eliding it for now as it doesn't affect the proof *)
      ⌜bv_unsigned b = 1 ⌝ ∗
      reg_col pkvm_sys_regs_updated ∗
      reg_col CNVZ_regs ∗
      "VBAR_EL2" ↦ᵣ RVal_Bits [BV{64} 116632] ∗
      True
    ) ∗
    instr_body (bv_unsigned elr) (
      "R0" ↦ᵣ RVal_Bits [BV{64} 0xbadca11] ∗
      reg_col pkvm_eret_sys_regs ∗
      reg_col CNVZ_regs ∗
      True
    ).
(*PROOF_END*)

(*SPEC_START*)
Definition spec `{!islaG Σ} `{!threadG} (sp stub_handler_addr offset: bv 64) (esr : bv 32) : iProp Σ :=
  ∃ (param el2_cont elr : bv 64) (spsr : bv 32),
  reg_col pkvm_sys_regs ∗
  reg_col mrs_regs ∗
  reg_col CNVZ_regs ∗
  reg_col rest_of_pstate ∗
  reg_col [(KindReg "EventRegister", BitsShape 1)] ∗
  reg_col [
    (KindReg "R2", BitsShape 64);
    (KindReg "R3", BitsShape 64);
    (KindReg "R4", BitsShape 64);
    (KindReg "R5", BitsShape 64);
    (KindReg "R6", BitsShape 64)
  ] ∗
  reg_col [(KindReg "VBAR_EL2", BitsShape 64)] ∗
  (* Move to pkvm_sys_regs *)
  "InGuardedPage" ↦ᵣ RVal_Bool false ∗
  "ESR_EL2" ↦ᵣ RVal_Bits esr ∗
  "R0" ↦ᵣ RVal_Bits param ∗
  "R1" ↦ᵣ RVal_Bits el2_cont ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
  "ELR_EL2" ↦ᵣ RVal_Bits elr ∗
  ⌜bv_extract 0 1 spsr = [BV{1} 1]⌝ ∗
  ⌜bv_extract 1 1 spsr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 2 2 spsr = [BV{2} 1]⌝ ∗
  ⌜bv_extract 4 1 spsr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 9 1 spsr = [BV{1} 1]⌝ ∗
  ⌜bv_extract 20 1 spsr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 55 1 elr = [BV{1} 0]⌝ ∗
  ⌜bv_extract 55 1 el2_cont = [BV{1} 0]⌝ ∗
  (* Don't handle this hypercall for now *)
  ⌜bv_unsigned param ≠ 2⌝ ∗
  (bv_unsigned sp - 16) ↦ₘ? 8 ∗
  (bv_unsigned sp - 8) ↦ₘ? 8 ∗
  ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
  ⌜bv_unsigned sp > 16⌝ ∗
  ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
  0x77f8 ↦ₘ stub_handler_addr ∗
  (instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 ≠ 22⌝ ∗ ∃ (v : bv 64), "R0" ↦ᵣ RVal_Bits v ∗ ⌜bv_unsigned v ≠ 22⌝ ∗ True) ∧
  instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 = 22⌝ ∗ ⌜Z.ge (bv_unsigned param) 3⌝ ∗ True)) ∗
  (* Possibly should handle that this address gets shifted (even if it's by zero in this code) *)
  instr_pre (bv_unsigned (bv_sub stub_handler_addr offset)) stub_handler_spec ∗
  instr_body (bv_unsigned el2_cont) (
    ⌜bv_unsigned param = 1⌝ ∗ reg_col pkvm_sys_regs_updated ∗
    reg_col CNVZ_regs ∗
    "VBAR_EL2" ↦ᵣ RVal_Bits [BV{64} 116632] ∗
    True
  ) ∗
  instr_body (bv_unsigned elr) (
    "R0" ↦ᵣ RVal_Bits [BV{64} 0xbadca11] ∗
    reg_col pkvm_eret_sys_regs ∗
    reg_col CNVZ_regs ∗
    True
  ).
(*SPEC_END*)

(* This is simpler than I was expecting, could probably write a tactic for these
   so they can be generated by the frontend *)
(*PROOF_START*)
Lemma a742c_spec `{!islaG Σ} `{!threadG} pc (b : bv 16):
  instr pc (Some (partial_trace (Val_Bits b) a742c)) -∗
  instr_body pc (movk_spec pc "R6" b 1).
Proof.
  iStartProof.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  change 18446744069414649855 with (Z.lor (Z.ones 32 ≪ 32) (Z.ones 16)).
  bits_simplify.
Time Qed.

Definition a742c_spec_inst `{!islaG Σ} `{!threadG} pc b :=
  entails_to_simplify_hyp 0 (a742c_spec pc b).
Global Existing Instance a742c_spec_inst.

Lemma a7430_spec `{!islaG Σ} `{!threadG} pc (b : bv 16):
  instr pc (Some (partial_trace (Val_Bits b) a7430)) -∗
  instr_body pc (movk_spec pc "R6" b 2).
Proof.
  iStartProof.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  change 18446462603027808255 with (Z.lor (Z.ones 16 ≪ 48) (Z.ones 32)).
  bits_simplify.
Time Qed.

Definition a7430_spec_inst `{!islaG Σ} `{!threadG} pc b :=
  entails_to_simplify_hyp 0 (a7430_spec pc b).
Global Existing Instance a7430_spec_inst.

Lemma a7434_spec `{!islaG Σ} `{!threadG} pc (b : bv 16):
  instr pc (Some (partial_trace (Val_Bits b) a7434)) -∗
  instr_body pc (movk_spec pc "R6" b 3).
Proof.
  iStartProof.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  bits_simplify.
Time Qed.

Definition a7434_spec_inst `{!islaG Σ} `{!threadG} pc b :=
  entails_to_simplify_hyp 0 (a7434_spec pc b).
Global Existing Instance a7434_spec_inst.

Definition load_offset_spec `{!islaG Σ} `{!threadG} offset pc_cont : iProp Σ :=
  reg_col pkvm_sys_regs ∗
  reg_col [(KindReg "R6", BitsShape 64)] ∗
  instr_body pc_cont (
    reg_col pkvm_sys_regs ∗
    "R6" ↦ᵣ RVal_Bits offset ∗
    True
  ).
(*PROOF_END*)

(*PROOF_START*)
Lemma load_offset_verif `{!islaG Σ} `{!threadG} (offset : bv 64) :
  instr 29736 (Some (partial_trace (Val_Bits (bv_extract 0 16 offset)) a7428)) ∗
  instr 29740 (Some (partial_trace (Val_Bits (bv_extract 16 16 offset)) a742c)) ∗
  instr 29744 (Some (partial_trace (Val_Bits (bv_extract 32 16 offset)) a7430)) ∗
  instr 29748 (Some (partial_trace (Val_Bits (bv_extract 48 16 offset)) a7434)) -∗
  instr_body 29736 (load_offset_spec offset 29752).
Proof.
  iStartProof.
  unfold load_offset_spec.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  bits_simplify.
Time Qed.
(*PROOF_END*)

Lemma wp `{!islaG Σ} `{!threadG} sp esr stub_handler_addr (offset : bv 64) :
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
  instr_body 29736 (load_offset_spec offset 29752) ∗
  (*instr 29736 (Some (partial_trace (Val_Bits (bv_extract 0 16 offset)) a7428)) ∗
  instr 29740 (Some (partial_trace (Val_Bits (bv_extract 16 16 offset)) a742c)) ∗
  instr 29744 (Some (partial_trace (Val_Bits (bv_extract 32 16 offset)) a7430)) ∗
  instr 29748 (Some (partial_trace (Val_Bits (bv_extract 48 16 offset)) a7434)) ∗ *)
  instr 29752 (Some a7438) ∗
  instr 29756 (Some a743c) -∗
  instr_body 0x7400 (spec sp stub_handler_addr offset esr).
Proof.
(*PROOF_START*)
  unfold spec.
  iStartProof.
  liARun.
  + iDestruct select (_ ∧ _)%I as "[? _]".
    liARun.
  + iDestruct select (_ ∧ _)%I as "[_ ?]".
    liARun.
  + unfold load_offset_spec.
    liARun.
    unfold stub_handler_spec.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  * contradict H13.
    rewrite H12.
    assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    by rewrite G.
  * assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    rewrite G in H12.
    by rewrite <- H12.
(*PROOF_END*)
Time Qed.

Lemma wp' `{!islaG Σ} `{!threadG} sp esr stub_handler_addr (offset : bv 64) :
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
  instr 29736 (Some (partial_trace (Val_Bits (bv_extract 0 16 offset)) a7428)) ∗
  instr 29740 (Some (partial_trace (Val_Bits (bv_extract 16 16 offset)) a742c)) ∗
  instr 29744 (Some (partial_trace (Val_Bits (bv_extract 32 16 offset)) a7430)) ∗
  instr 29748 (Some (partial_trace (Val_Bits (bv_extract 48 16 offset)) a7434)) ∗
  instr 29752 (Some a7438) ∗
  instr 29756 (Some a743c) -∗
  instr_body 0x7400 (spec sp stub_handler_addr offset esr).
Proof.
(*PROOF_START*)
  iIntros "[? [? [? [? [? [? [? [? [? [? [i1 [i2 [i3 [i4 [? ?]]]]]]]]]]]]]]]".
  iAssert (instr_body 29736 (load_offset_spec offset 29752)) with "[i1 i2 i3 i4]" as "Hoffset".
  + iApply load_offset_verif.
    iFrame.
  + iApply wp. iFrame.
(*PROOF_END*)
Qed.

Lemma reset_wp `{!islaG Σ} `{!threadG} :
  instr 98888 (Some a18248) ∗
  instr 98892 (Some a1824c) ∗
  instr 98896 (Some a18250) ∗
  instr 98900 (Some a18254) ∗
  instr 98904 (Some a18258) ∗
  instr 98908 (Some a1825c) ∗
  instr 98912 (Some a18260) ∗
  instr 98916 (Some a18264) ∗
  instr 98920 (Some a18268) ∗
  instr 98924 (Some a1826c) ∗
  instr 98928 (Some a18270) ∗
  instr 98932 (Some a18274) ∗
  instr 98936 (Some a18278) ∗
  instr 98940 (Some a1827c) ∗
  instr 98944 (Some a18280) ∗
  instr 98948 (Some a18284) -∗
  instr_body 0x18248 reset_spec.
Proof.
(*PROOF_START*)
  unfold reset_spec.
  iStartProof.
  do 500 liAStep; liShow.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  + assert (Hshift: bv_shiftr spsr [BV{32} 0] = spsr); [by bits_simplify|].
    rewrite Hshift.
    rewrite H0.
    by bits_simplify.
  + bits_simplify.
    bitify_hyp H4.
    specialize (H4 n44 ltac:(lia)).
    bits_simplify_hyp H4.
    rewrite <- H4.
    f_equal.
    lia.
(*PROOF_END*)
Qed.



Lemma stub_handler_wp `{!islaG Σ} `{!threadG} :
  instr 98840 (Some a18218) ∗
  instr 98844 (Some a1821c) ∗
  instr 98848 (Some a18220) ∗
  instr 98852 (Some a18224) ∗
  instr 98856 (Some a18228) ∗
  instr 98860 (Some a1822c) ∗
  instr 98864 (Some a18230) ∗
  instr 98868 (Some a18234) ∗
  instr 98872 (Some a18238) ∗
  instr 98876 (Some a1823c) ∗
  instr 98880 (Some a18240) ∗
  instr 98884 (Some a18244) ∗
  instr_body 0x18248 reset_spec ∗
  instr 98952 (Some a18288) ∗
  instr 98956 (Some a1828c) ∗
  instr 98960 (Some a18290) -∗
  instr_body 0x18218 (stub_handler_spec).
Proof.
(*PROOF_START*)
  unfold stub_handler_spec.
  iStartProof.
  liARun.
  + unfold reset_spec.
    liARun.
  + (* This branch is a contradiction, but for now just let the proof proceed and contradict it later? *)
    unfold reset_spec.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  * assert (Hshift: bv_shiftr spsr [BV{32} 0] = spsr); [by bits_simplify|].
    rewrite Hshift.
    rewrite H0.
    by bits_simplify.
  * bits_simplify.
    bitify_hyp H4.
    specialize (H4 n ltac:(lia)).
    bits_simplify_hyp H4.
    rewrite <- H4.
    f_equal.
    lia.
(*PROOF_END*)
Qed.
