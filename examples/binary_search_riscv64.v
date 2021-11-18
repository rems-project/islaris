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
(* This was in part funded from the European Research Council (ERC) under   *)
(* the European Union's Horizon 2020 research and innovation programme      *)
(* (grant agreement No 789108, "ELVER"), in part supported by the UK        *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), and in part funded by Google.           *)
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

Require Import isla.riscv64.riscv64.
From isla.instructions.binary_search_riscv64 Require Import instrs.

Section proof.
Context `{!islaG Σ} `{!threadG}.

(*SPEC_START*)
Definition comp_spec (stack_size : Z) (R : bv 64 → bv 64 → Prop) (P : iProp Σ) : iProp Σ :=
  (c_call stack_size (λ args sp RET,
     P ∗
     RET (λ rets, ∃ b : bool, ⌜rets !!! 0%nat = bool_to_bv 64 b⌝ ∗ ⌜b ↔ R (args !!! 0%nat) (args !!! 1%nat)⌝ ∗ P ∗ True)
  ))%I.
(*SPEC_END*)
Typeclasses Opaque comp_spec.
Global Instance : LithiumUnfold (comp_spec) := I.

Lemma compare_int_spec :
  instr 0x00000000103000a0 (Some aa0) -∗
  instr 0x00000000103000a4 (Some aa4) -∗
  instr 0x00000000103000a8 (Some aa8) -∗
(*SPEC_START*)
  instr_body 0x00000000103000a0 (comp_spec 0 (λ x y, bv_unsigned x ≤ bv_unsigned y) (True)).
(*SPEC_END*)
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  liInst Hevar (bv_unsigned b10 <=? bv_unsigned b11). rewrite Zleb_bool_decide.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - bv_simplify. repeat case_bool_decide => //; bv_solve.
  - naive_solver.
(*PROOF_END*)
Time Qed.

(*PROOF_START*)
Definition binary_search_loop_spec : iProp Σ :=
  ∃ (x l r comp xs tmp1 sp : bv 64) (data : list (bv 64)),
  ∃ stack_size R P,
  reg_col sys_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> ["x1"; "x5"; "x6"; "x7"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29"; "x30"; "x31" ]) ∗
  "x8" ↦ᵣ RVal_Bits tmp1 ∗
  "x9" ↦ᵣ RVal_Bits l ∗
  "x18" ↦ᵣ RVal_Bits x ∗
  "x19" ↦ᵣ RVal_Bits xs ∗
  "x20" ↦ᵣ RVal_Bits comp ∗
  "x21" ↦ᵣ RVal_Bits r ∗
  "x22" ↦ᵣ: λ r22, ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
  "x23" ↦ᵣ: λ r23, ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
  "x24" ↦ᵣ: λ r24, ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
  "x25" ↦ᵣ: λ r25, ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "x26" ↦ᵣ: λ r26, ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "x27" ↦ᵣ: λ r27, ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "x2" ↦ᵣ RVal_Bits sp ∗
  bv_unsigned xs ↦ₘ∗ data ∗
  □ instr_pre (bv_unsigned comp) (comp_spec stack_size R P) ∗
  ⌜bv_extract 0 1 comp = [BV{1} 0]⌝ ∗ ⌜bv_extract 1 1 comp = [BV{1} 0]⌝ ∗
  ⌜bv_unsigned l < bv_unsigned r ≤ length data⌝ ∗
  ⌜bv_unsigned xs `mod` 8 = 0⌝ ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  P ∗
  ⌜0x0000000080000000 ≤ bv_unsigned xs ∧ bv_unsigned xs + (length data) * 8 < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned sp - stack_size ∧ bv_unsigned sp < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜StronglySorted R data⌝ ∗ ⌜Transitive R⌝ ∗
  ⌜∀ (i : nat) y, i < bv_unsigned l → data !! i = Some y → R y x⌝ ∗
  ⌜∀ (i : nat) y, bv_unsigned r ≤ i → data !! i = Some y → ¬ R y x⌝ ∗
  instr_pre 0x0000000010300078 (
    ∃ (l' r' tmp1 : bv 64),
      reg_col sys_regs ∗
      reg_col ((λ r, (KindReg r, BitsShape 64)) <$> ["x1"; "x5"; "x6"; "x7"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17"; "x28"; "x29"; "x30"; "x31" ]) ∗
     "x8" ↦ᵣ RVal_Bits tmp1 ∗
     "x9" ↦ᵣ RVal_Bits l' ∗
     "x18" ↦ᵣ RVal_Bits x ∗
     "x19" ↦ᵣ RVal_Bits xs ∗
     "x20" ↦ᵣ RVal_Bits comp ∗
     "x21" ↦ᵣ RVal_Bits r' ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x22" ↦ᵣ r22 ∗
     "x23" ↦ᵣ r23 ∗
     "x24" ↦ᵣ r24 ∗
     "x25" ↦ᵣ r25 ∗
     "x26" ↦ᵣ r26 ∗
     "x27" ↦ᵣ r27 ∗
      bv_unsigned xs ↦ₘ∗ data ∗
      P ∗
      (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
      ⌜∀ (i : nat) y, i < bv_unsigned l' → data !! i = Some y → R y x⌝ ∗
      ⌜∀ (i : nat) y, bv_unsigned l' ≤ i → data !! i = Some y → ¬ R y x⌝ ∗
      True
  )
.
Global Instance : LithiumUnfold (binary_search_loop_spec) := I.

Lemma binary_search_cond_1 {A} y R (l : list A) i j x z `{!Transitive R}:
  R y z → StronglySorted R l → l !! i = Some x → l !! j = Some y → (i ≤ j)%nat → R x z.
Proof.
  move => ?????.
  have [||||->|?]:= StronglySorted_lookup_le R l i j x y => //. by etrans.
Qed.

Lemma binary_search_cond_2 {A} y R (l : list A) i j x z `{!Transitive R}:
  ¬ R y z → StronglySorted R l → l !! i = Some x → l !! j = Some y → (j ≤ i)%nat → ¬ R x z.
Proof.
  move => Hneg ????. have [||||<-|?]:= StronglySorted_lookup_le R l j i y x => //.
  contradict Hneg. by etrans.
Qed.
(*PROOF_END*)

Lemma binary_search_loop :
  instr 0x000000001030003c (Some a3c) -∗
  instr 0x0000000010300040 (Some a40) -∗
  instr 0x0000000010300044 (Some a44) -∗
  instr 0x0000000010300048 (Some a48) -∗
  instr 0x000000001030004c (Some a4c) -∗
  instr 0x0000000010300050 (Some a50) -∗
  instr 0x0000000010300054 (Some a54) -∗
  instr 0x0000000010300058 (Some a58) -∗
  instr 0x000000001030005c (Some a5c) -∗
  instr 0x0000000010300060 (Some a60) -∗
  instr 0x0000000010300064 (Some a64) -∗
  instr 0x0000000010300068 (Some a68) -∗
  instr 0x000000001030006c (Some a6c) -∗
  instr 0x0000000010300070 (Some a70) -∗
  □ instr_pre 0x0000000010300044 binary_search_loop_spec -∗
  instr_body 0x0000000010300044 binary_search_loop_spec.
Proof.
(*PROOF_START*)
  iStartProof.
  liARun.
  liInst Hevar (Z.to_nat (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2)).
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try (rename select (_ ↔ R _ _) into HR).
  all: try (rewrite bv_sign_extend_idemp bv_add_0_r in HR; [|done]).
  - bv_simplify_arith_hyp select (_ >= _).
    apply: binary_search_cond_2; [solve_goal..| bv_solve].
  - bv_simplify_arith_hyp select (¬ (_ >= _)). bv_solve.
  - bv_simplify_arith_hyp select (¬ (_ >= _)).
    bv_simplify_arith_hyp select (_ ≤ _).
    apply: binary_search_cond_2; [solve_goal..| bv_solve].
  - bv_simplify_arith_hyp select (_ < _). bv_solve.
  - bv_simplify_arith_hyp select (_ < _).
    apply: binary_search_cond_1; [solve_goal..| bv_solve].
  - bv_simplify_arith_hyp select (_ < _).
    apply: binary_search_cond_1; [solve_goal..| bv_solve].
  - bv_simplify_arith_hyp select (_ ≤ _).
    bv_simplify_arith_hyp select (¬ (_ < _)).
    naive_solver bv_solve.
(*PROOF_END*)
Time Qed.


(*SPEC_START*)
Definition binary_search_spec (stack_size : Z) : iProp Σ :=
  (c_call (stack_size + 64) (λ args sp RET,
    ∃ (data : list (bv 64)) R P,
    □ instr_pre (bv_unsigned (args !!! 0%nat)) (comp_spec stack_size R P) ∗
    bv_unsigned (args !!! 1%nat) ↦ₘ∗ data ∗
    P ∗
    ⌜bv_unsigned (args !!! 2%nat) = length data⌝ ∗
    ⌜bv_unsigned (args !!! 1%nat) `mod` 8 = 0⌝ ∗
    ⌜bv_extract 0 1 (args !!! 0%nat) = [BV{1} 0]⌝ ∗ ⌜bv_extract 1 1 (args !!! 0%nat) = [BV{1} 0]⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned (args !!! 1%nat) ∧ bv_unsigned (args !!! 1%nat) + (length data) * 8 < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    ⌜StronglySorted R data⌝ ∗ ⌜Transitive R⌝ ∗
    RET (λ rets,
      bv_unsigned (args !!! 1%nat) ↦ₘ∗ data ∗
      P ∗
      ⌜∀ (i : nat) y, i < bv_unsigned (rets !!! 0%nat) → data !! i = Some y → R y (args !!! 3%nat)⌝ ∗
      ⌜∀ (i : nat) y, bv_unsigned (rets !!! 0%nat) ≤ i → data !! i = Some y → ¬ R y (args !!! 3%nat)⌝ ∗
      True))
  )%I.
(*SPEC_END*)
Global Instance : LithiumUnfold (binary_search_spec) := I.

Lemma binary_search stack_size :
(*SPEC_START*)
  0 ≤ stack_size →
(*SPEC_END*)
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
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗

  instr 0x0000000010300074 (Some a74) -∗
  instr 0x0000000010300078 (Some a78) -∗
  instr 0x000000001030007c (Some a7c) -∗
  instr 0x0000000010300080 (Some a80) -∗
  instr 0x0000000010300084 (Some a84) -∗
  instr 0x0000000010300088 (Some a88) -∗
  instr 0x000000001030008c (Some a8c) -∗
  instr 0x0000000010300090 (Some a90) -∗
  instr 0x0000000010300094 (Some a94) -∗
  instr 0x0000000010300098 (Some a98) -∗
  instr 0x000000001030009c (Some a9c) -∗
  □ instr_pre 0x0000000010300044 binary_search_loop_spec -∗
  instr_body 0x0000000010300000 (binary_search_spec stack_size).
Proof.
(*PROOF_START*)
  move => ?. iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try rewrite ->@bv_add_0_r in * by done; try done.
  all: try bv_solve.
  - bv_simplify_hyp select (_ ≠ [BV{64} 0]). bv_solve.
  - eauto.
  - eauto.
(*PROOF_END*)
Time Qed.

End proof.
