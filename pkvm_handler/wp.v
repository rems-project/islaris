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

Definition instrs_iprop `{!islaG Σ} `{!threadG} := ([∗ list] i ∈ instr_map, instr i.1 (Some i.2))%I.

(*PROOF_START*)
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
  liARun.
  Unshelve.
  all: try (repeat f_equal; bv_solve).
  all: prepare_sidecond; bv_solve.
Time Qed.
(*PROOF_END*)

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
(*SPEC_END*)

(*PROOF_START*)
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
  liARun.
  Unshelve.
  (* TODO: Check if bv_solve on the latest branch solves this, otherwise fix it *)
  all: prepare_sidecond.
  bv_solve.
Time Qed.

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
  liARun.
  Unshelve.
  all: prepare_sidecond.
  by bits_simplify.
Time Qed.
(*PROOF_END*)

(*SPEC_START*)
Definition spec `{!islaG Σ} `{!threadG} (sp stub_handler_addr offset: bv 64) (esr : bv 32) : iProp Σ :=
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
  0x77f8 ↦ₘ stub_handler_addr ∗
  (instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 ≠ 22⌝ ∗ ∃ (v : bv 64), "R0" ↦ᵣ RVal_Bits v ∗ ⌜bv_unsigned v ≠ 22⌝ ∗ True) ∧
  instr_pre 0x6800 (⌜Z.shiftr (bv_unsigned esr) 26 = 22⌝ ∗ ⌜Z.ge (bv_unsigned v0) 3⌝ ∗ True)) ∗
  (* Possibly should handle that this address gets shifted (even if it's by zero in this code) *)
  instr_pre (bv_unsigned (bv_sub stub_handler_addr offset)) (
    ⌜Z.shiftr (bv_unsigned esr) 26 = 22⌝ ∗
    ⌜Z.lt (bv_unsigned v0) 3⌝ ∗
    "SP_EL2" ↦ᵣ RVal_Bits sp ∗
    "R5" ↦ᵣ RVal_Bits (bv_sub stub_handler_addr offset)∗
    "R6" ↦ᵣ RVal_Bits offset ∗
    True).
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
  ∃ v,
  reg_col sys_regs ∗
  "R6" ↦ᵣ v ∗
  instr_body pc_cont (
    reg_col sys_regs ∗
    "R6" ↦ᵣ RVal_Bits offset ∗
    True
  ).

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
  Unshelve.
  all: prepare_sidecond.
  all: try bv_solve.
  * contradict H4.
    rewrite H3.
    rewrite <- H4.
    by bits_simplify.
  * rewrite <- H4.
    assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    by rewrite G in H3.
  * rewrite <- H4.
    assert(G: bv_unsigned (bv_concat 64 [BV{32} 0] esr) = bv_unsigned esr); [bv_solve|].
    by rewrite G in H3.
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
  iIntros "[? [? [? [? [? [? [? [? [? [? [i1 [i2 [i3 [i4 [? ?]]]]]]]]]]]]]]]".
  iAssert (instr_body 29736 (load_offset_spec offset 29752)) with "[i1 i2 i3 i4]" as "Hoffset".
  + iApply load_offset_verif.
    iFrame.
  + iApply wp. iFrame.
Qed.
