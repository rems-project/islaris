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
From isla.instructions Require Import instr_str_unaligned.

(* This is necessary for gathering data, please leave it here. *)
Compute (isla_trace_length instr_str_unaligned).

Section proof.
Context `{!islaG Σ} `{!threadG}.

Record pstate_record := PSTATE {
  PSTATE_SP    : bv 1;
  PSTATE_EL    : bv 2;
  PSTATE_nRW   : bv 1;
  PSTATE_F     : bv 1;
  PSTATE_I     : bv 1;
  PSTATE_A     : bv 1;
  PSTATE_D     : bv 1;
  PSTATE_BTYPE : bv 2;
  PSTATE_SBSS  : bv 1;
  PSTATE_IL    : bv 1;
  PSTATE_SS    : bv 1;
  PSTATE_PAN   : bv 1;
  PSTATE_UAO   : bv 1;
  PSTATE_DIT   : bv 1;
  PSTATE_TCO   : bv 1;
  PSTATE_V     : bv 1;
  PSTATE_C     : bv 1;
  PSTATE_Z     : bv 1;
  PSTATE_N     : bv 1;
}.

Definition pstate_to_reg_col  (s : pstate_record) : list (reg_kind * valu_shape) := [
  (KindField "PSTATE" "SP"   , ExactShape (RVal_Bits s.(PSTATE_SP   )));
  (KindField "PSTATE" "EL"   , ExactShape (RVal_Bits s.(PSTATE_EL   )));
  (KindField "PSTATE" "nRW"  , ExactShape (RVal_Bits s.(PSTATE_nRW  )));
  (KindField "PSTATE" "F"    , ExactShape (RVal_Bits s.(PSTATE_F    )));
  (KindField "PSTATE" "I"    , ExactShape (RVal_Bits s.(PSTATE_I    )));
  (KindField "PSTATE" "A"    , ExactShape (RVal_Bits s.(PSTATE_A    )));
  (KindField "PSTATE" "D"    , ExactShape (RVal_Bits s.(PSTATE_D    )));
  (KindField "PSTATE" "BTYPE", ExactShape (RVal_Bits s.(PSTATE_BTYPE)));
  (KindField "PSTATE" "SBSS" , ExactShape (RVal_Bits s.(PSTATE_SBSS )));
  (KindField "PSTATE" "IL"   , ExactShape (RVal_Bits s.(PSTATE_IL   )));
  (KindField "PSTATE" "SS"   , ExactShape (RVal_Bits s.(PSTATE_SS   )));
  (KindField "PSTATE" "PAN"  , ExactShape (RVal_Bits s.(PSTATE_PAN  )));
  (KindField "PSTATE" "UAO"  , ExactShape (RVal_Bits s.(PSTATE_UAO  )));
  (KindField "PSTATE" "DIT"  , ExactShape (RVal_Bits s.(PSTATE_DIT  )));
  (KindField "PSTATE" "TCO"  , ExactShape (RVal_Bits s.(PSTATE_TCO  )));
  (KindField "PSTATE" "V"    , ExactShape (RVal_Bits s.(PSTATE_V    )));
  (KindField "PSTATE" "C"    , ExactShape (RVal_Bits s.(PSTATE_C    )));
  (KindField "PSTATE" "Z"    , ExactShape (RVal_Bits s.(PSTATE_Z    )));
  (KindField "PSTATE" "N"    , ExactShape (RVal_Bits s.(PSTATE_N    )))
].

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

(*SPEC_START*)
Definition spsr_of_pstate (s : pstate_record) : bv 32 :=
  let fields :=
    [ bv_shiftl (bv_zero_extend 32 s.(PSTATE_N    )) (BV 32 31);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_Z    )) (BV 32 30);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_C    )) (BV 32 29);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_V    )) (BV 32 28);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_TCO  )) (BV 32 25);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_DIT  )) (BV 32 24);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_UAO  )) (BV 32 23);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_PAN  )) (BV 32 22);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_SS   )) (BV 32 21);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_IL   )) (BV 32 20);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_SBSS )) (BV 32 12);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_BTYPE)) (BV 32 10);
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_D    )) (BV 32 9 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_A    )) (BV 32 8 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_I    )) (BV 32 7 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_F    )) (BV 32 6 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_nRW  )) (BV 32 5 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_EL   )) (BV 32 2 );
      bv_shiftl (bv_zero_extend 32 s.(PSTATE_SP   )) (BV 32 0 ) ]
  in
  fold_left bv_or fields (BV 32 0).

Definition exception_pstate (s : pstate_record) := {|
  PSTATE_SP    := s.(PSTATE_SP);
  PSTATE_EL    := s.(PSTATE_EL);
  PSTATE_nRW   := s.(PSTATE_nRW);
  PSTATE_F     := (BV 1 1);
  PSTATE_I     := (BV 1 1);
  PSTATE_A     := (BV 1 1);
  PSTATE_D     := (BV 1 1);
  PSTATE_BTYPE := s.(PSTATE_BTYPE);
  PSTATE_SBSS  := s.(PSTATE_SBSS);
  PSTATE_IL    := (BV 1 0);
  PSTATE_SS    := (BV 1 0);
  PSTATE_PAN   := s.(PSTATE_PAN);
  PSTATE_UAO   := s.(PSTATE_UAO);
  PSTATE_DIT   := s.(PSTATE_DIT);
  PSTATE_TCO   := s.(PSTATE_TCO);
  PSTATE_V     := s.(PSTATE_V);
  PSTATE_C     := s.(PSTATE_C);
  PSTATE_Z     := s.(PSTATE_Z);
  PSTATE_N     := s.(PSTATE_N);
|}.

Definition bunch_of_sys_regs :=
  let with_value :=
    [ ("CFG_ID_AA64PFR0_EL1_EL0", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL1", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL2", RVal_Bits (BV 4 1))
    ; ("CFG_ID_AA64PFR0_EL1_EL3", RVal_Bits (BV 4 1))
    ; ("HCR_EL2"  , RVal_Bits (BV 64 0x0000000080000000))
    ; ("SCR_EL3"  , RVal_Bits (BV 32 0x00000501))
    ; ("SCTLR_EL2", RVal_Bits (BV 64 0x0000000004000002))
    ; ("TCR_EL2", RVal_Bits (BV 64 0)) ]
  in
  (λ '(r, v), (KindReg r, ExactShape v)) <$> with_value.
(*SPEC_END*)

Lemma str_unaligned pstate (esr spsr elr far hpfar : bv 64) v0 v1 :
(*SPEC_START*)
  pstate.(PSTATE_EL) = (BV 2 2) →
  pstate.(PSTATE_SP) = (BV 1 1) →
  pstate.(PSTATE_nRW) = (BV 1 0) →
  pstate.(PSTATE_BTYPE) = (BV 2 0) →
  pstate.(PSTATE_SBSS) = (BV 1 0) →
  pstate.(PSTATE_UAO) = (BV 1 0) →
  pstate.(PSTATE_DIT) = (BV 1 0) →
  pstate.(PSTATE_TCO) = (BV 1 0) →
  bv_and v1 (BV 64 0xfff0000000000007) = (BV 64 0x0000000000000001) →
(*SPEC_END*)
  instr 0x0 (Some instr_str_unaligned) -∗
  instr_body 0x0 (
(*SPEC_START*)
    "VBAR_EL2" ↦ᵣ RVal_Bits (BV 64 0x0) ∗
    "ESR_EL2" ↦ᵣ RVal_Bits esr ∗
    "SPSR_EL2" ↦ᵣ RVal_Bits spsr ∗
    "ELR_EL2" ↦ᵣ RVal_Bits elr ∗
    "FAR_EL2" ↦ᵣ RVal_Bits far ∗
    "HPFAR_EL2" ↦ᵣ RVal_Bits hpfar ∗
    "R0" ↦ᵣ RVal_Bits v0 ∗
    "R1" ↦ᵣ RVal_Bits v1 ∗
    reg_col (pstate_to_reg_col pstate) ∗
    reg_col bunch_of_sys_regs ∗
    instr_pre 0x200 (
      "VBAR_EL2" ↦ᵣ RVal_Bits (BV 64 0x0) ∗
      (* Use a boolean to acount for undefined bit. FIXME use more general infrastructure. *)
      (∃ b : bool, "ESR_EL2" ↦ᵣ RVal_Bits (if b then (BV 32 0x96000061) else (BV 32 0x960000e1))) ∗
      "SPSR_EL2" ↦ᵣ RVal_Bits (spsr_of_pstate pstate) ∗
      "ELR_EL2" ↦ᵣ RVal_Bits (BV 64 0x0) ∗ (* address of faulting instruciton. *)
      "FAR_EL2" ↦ᵣ RVal_Bits v1 ∗
      (* Use bitvector to account for undefined bits. FIXME use more general infrastructure. *)
      (∃ v : bv 40, "HPFAR_EL2" ↦ᵣ RVal_Bits (bv_or (bv_and hpfar (BV 64 0xfffff0000000000f))
                                                    (bv_shiftl (bv_zero_extend 64 v) (BV 64 4)))) ∗
      "R0" ↦ᵣ RVal_Bits v0 ∗
      "R1" ↦ᵣ RVal_Bits v1 ∗
      reg_col (pstate_to_reg_col (exception_pstate pstate)) ∗
      True
(*SPEC_END*)
    )
  ).
Proof.
(*PROOF_START*)
  destruct pstate. move => /= -> -> -> -> -> -> -> ->.
  rewrite /pstate_to_reg_col /spsr_of_pstate /=. move => *.
  iStartProof.
  liARun.
  - liInst (λ x, x.1ₗ = false). liARun.
  - liInst (λ x, x.1ₗ = true). liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: bv_simplify; f_equal.
  + rewrite !Z.lor_assoc !Z.land_lor_distr_l -!Z.land_assoc.
    repeat match goal with |- context [Z.land ?a ?b] => reduce_closed (Z.land a b) end.

    apply Z.bits_inj_iff'; intros i => ?.
    bitblast_unfold.
    bitblast_bool_decide_simplify.
    destruct (decide ((i < 22))); bitblast_bool_decide_simplify.
    * destruct (decide ((i < 9))); bitblast_bool_decide_simplify.
      all: bitblast; f_equal; lia.
    * destruct (decide ((i < 29))); bitblast_bool_decide_simplify.
      all: bitblast; f_equal; lia.
  + rewrite !Z.lor_assoc !Z.land_lor_distr_l -!Z.land_assoc.
    repeat match goal with |- context [Z.land ?a ?b] => reduce_closed (Z.land a b) end.

    apply Z.bits_inj_iff'; intros i => ?.
    bitblast_unfold.
    bitblast_bool_decide_simplify.
    destruct (decide ((i < 22))); bitblast_bool_decide_simplify.
    * destruct (decide ((i < 9))); bitblast_bool_decide_simplify.
      all: bitblast; f_equal; lia.
    * destruct (decide ((i < 29))); bitblast_bool_decide_simplify.
      all: bitblast; f_equal; lia.
(*PROOF_END*)
Time Qed.

End proof.
