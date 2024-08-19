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
From isla.instructions.memcpy Require Import instrs.


(*
C code:
    void mcpy(unsigned char *dest, unsigned char *src, size_t n) {
      for(size_t i = 0; i < n; i++ ) {
        dest[i] = src[i];
      }
    }

ASM: (generated via ARM64 gcc 11.2 -O2, https://godbolt.org/z/v8d7ecbhc)
0000000000000000 <mcpy>:
   0:	b40000e2 	cbz	x2, 1c <mcpy+0x1c>
   4:	d2800003 	mov	x3, #0x0                   	// #0
   8:	38636824 	ldrb	w4, [x1, x3]
   c:	38236804 	strb	w4, [x0, x3]
  10:	91000463 	add	x3, x3, #0x1
  14:	eb03005f 	cmp	x2, x3
  18:	54ffff81 	b.ne	8 <mcpy+0x8>  // b.any
  1c:	d65f03c0 	ret

The code can be generated with
$ PATH=$PWD/bin:$PATH dune exec -- islaris examples/memcpy.dump -d -o instructions  -n "a{op}" --coqdir=isla.instructions

*)

(*PROOF_START*)
Definition memcpy_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst i n : bv 64) (srcdata dstdata : list byte),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
  "R3" ↦ᵣ RVal_Bits i ∗ "R4" ↦ᵣ RVal_Bits tmp ∗
  bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
  ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
  ⌜bv_unsigned i < bv_unsigned n⌝ ∗
  ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜take (Z.to_nat (bv_unsigned i)) dstdata = take (Z.to_nat (bv_unsigned i)) srcdata⌝ ∗
  instr_pre 0x000000001030001c (
    ∃ (tmp n : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
      "R4" ↦ᵣ RVal_Bits tmp ∗ "R3" ↦ᵣ RVal_Bits n ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
  )
.
(*PROOF_END*)

Arguments memcpy_loop_spec /.

Lemma memcpy_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  □ instr_pre 0x0000000010300008 memcpy_loop_spec -∗
  instr_body 0x0000000010300008 memcpy_loop_spec.
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.

  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith select (bv_extract _ _ _ = _).
  - rewrite length_insert. bv_solve.
  - bv_solve.
  - bv_simplify.
    rewrite bv_wrap_small; [|bv_solve].
    have ->: (Z.to_nat (bv_unsigned i + 1)) = S ((Z.to_nat (bv_unsigned i))) by bv_solve.
    erewrite take_S_r. 2: { erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
    erewrite take_S_r. 2: { rewrite <- H6. f_equal. bv_solve. }
    rewrite take_insert; [|bv_solve].
    f_equal; [done|]. f_equal. bv_solve.
  - bv_solve.
  - rewrite -(take_drop (Z.to_nat (bv_unsigned i)) (<[_ := _]> _)).
    rewrite -(take_drop (Z.to_nat (bv_unsigned i)) srcdata).
    f_equal.
    + rewrite take_insert; [done|bv_solve].
    + erewrite drop_S. 2: { erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
      erewrite (drop_S srcdata). 2: { rewrite <- H6. f_equal. bv_solve. }
      rewrite !drop_ge ?length_insert; [ |bv_solve..].
      f_equal. bv_solve.
(*PROOF_END*)
Time Qed.

Lemma memcpy `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300008 memcpy_loop_spec -∗
(*SPEC_START*)
  instr_body 0x0000000010300000 (
    ∃ (tmp1 tmp2 src dst n ret : bv 64) (srcdata dstdata : list byte),
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
    "R3" ↦ᵣ RVal_Bits tmp2 ∗ "R4" ↦ᵣ RVal_Bits tmp1 ∗
    "R30" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
    ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp1 tmp2 n : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
      "R3" ↦ᵣ RVal_Bits tmp2 ∗ "R4" ↦ᵣ RVal_Bits tmp1 ∗
      "R30" ↦ᵣ RVal_Bits ret ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
(*SPEC_END*)
  )).
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  - by destruct dstdata, srcdata.
  - bv_simplify select (n ≠ _). bv_solve.
(*PROOF_END*)
Time Qed.
