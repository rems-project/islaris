Require Import isla.aarch64.aarch64.
From isla.instructions.binary_search Require Import instrs. Compute (sum_list (isla_trace_length <$> instr_map.*2)).

Section proof.
Context `{!islaG Σ} `{!threadG}.

(* TODO: allow the function to use the stack? *)
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
  instr 0x0000000010300074 (Some a74) -∗
  instr 0x0000000010300078 (Some a78) -∗
  instr 0x000000001030007c (Some a7c) -∗
(*SPEC_START*)
  instr_body 0x0000000010300074 (comp_spec 0 (λ x y, bv_unsigned x ≤ bv_unsigned y) (True)).
(*SPEC_END*)
Proof.
(*PROOF_START*)
  iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - revert select (_ ≠@{bv _} _) => /bv_eq. bv_solve.
(*PROOF_END*)
Qed.

(*PROOF_START*)
Definition a40_tst_imm_spec : iProp Σ :=
  ∃ (v : bv 64),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits v ∗
  instr_pre 0x0000000010300044 (
    reg_col sys_regs ∗
    "R0" ↦ᵣ RVal_Bits v ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits [BV{1} 0] ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits (bv_not (bv_extract 0 1 v)) ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits [BV{1} 0] ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits [BV{1} 0] ∗
    True
  ).
Global Instance : LithiumUnfold (a40_tst_imm_spec) := I.

Lemma a40_has_tst_imm_spec :
  instr 0x0000000010300040 (Some a40) -∗
  instr_body 0x0000000010300040 (a40_tst_imm_spec).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - bv_simplify.
    rewrite Z.shiftr_eq_0 // ?Z.land_nonneg; [lia|].
    apply: Z.le_lt_trans; [apply Z.log2_land; bv_solve| bv_solve].
  - bits_simplify.
    bitify_hyp H0.
    specialize (H0 n ltac:(lia)).
    bits_simplify_hyp H0.
    by rewrite H0.
  - bv_simplify.
    rewrite Z.shiftr_eq_0 // ?Z.land_nonneg; [lia|].
    apply: Z.le_lt_trans; [apply Z.log2_land; bv_solve| bv_solve].
  - bits_simplify.
    assert(H0' : Z.testbit (bv_unsigned (bv_and (bv_extract 0 32 v) [BV{32} 1])) 0 ≠ Z.testbit (bv_unsigned [BV{32} 0]) 0).
    + contradict H0.
      bits_simplify.
      bits_simplify_hyp H0.
      assert (Hz : n0 = 0); [lia|].
      by rewrite Hz.
    + bits_simplify_hyp H0'.
      assert(Hz : n = 0); [lia|].
      rewrite Hz.
      apply not_false_is_true in H0'.
      by rewrite H0'.
Qed.

Definition binary_search_loop_spec : iProp Σ :=
  ∃ (x l r comp xs tmp2 sp : bv 64) (data : list (bv 64)),
  ∃ stack_size R P,
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (KindReg r, BitsShape 64)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R29"; "R30" ]) ∗
  "R19" ↦ᵣ RVal_Bits x ∗
  "R20" ↦ᵣ RVal_Bits r ∗
  "R21" ↦ᵣ RVal_Bits xs ∗
  "R22" ↦ᵣ RVal_Bits comp ∗
  "R23" ↦ᵣ RVal_Bits l ∗
  "R24" ↦ᵣ RVal_Bits tmp2 ∗
  "R25" ↦ᵣ: λ r25, ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
  "R26" ↦ᵣ: λ r26, ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
  "R27" ↦ᵣ: λ r27, ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
  "R28" ↦ᵣ: λ r28, ⌜valu_has_shape r28 (BitsShape 64)⌝ ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  bv_unsigned xs ↦ₘ∗ data ∗
  □ instr_pre (bv_unsigned comp) (comp_spec stack_size R P) ∗
  P ∗
  ⌜stack_size < bv_unsigned sp < 2 ^ 52⌝ ∗
  (bv_unsigned sp - stack_size) ↦ₘ? stack_size ∗
  ⌜bv_unsigned l < bv_unsigned r ≤ length data⌝ ∗
  ⌜bv_unsigned xs `mod` 8 = 0⌝ ∗
  ⌜bv_unsigned xs + (length data) * 8 < 2 ^ 52⌝ ∗
  ⌜StronglySorted R data⌝ ∗ ⌜Transitive R⌝ ∗
  ⌜∀ (i : nat) y, i < bv_unsigned l → data !! i = Some y → R y x⌝ ∗
  ⌜∀ (i : nat) y, bv_unsigned r ≤ i → data !! i = Some y → ¬ R y x⌝ ∗
  instr_pre 0x0000000010300054 (
    ∃ (l' r' tmp2 : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (KindReg r, BitsShape 64)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R29"; "R30" ]) ∗
      "R19" ↦ᵣ RVal_Bits x ∗
      "R20" ↦ᵣ RVal_Bits r' ∗
      "R21" ↦ᵣ RVal_Bits xs ∗
      "R22" ↦ᵣ RVal_Bits comp ∗
      "R23" ↦ᵣ RVal_Bits l' ∗
      "R24" ↦ᵣ RVal_Bits tmp2 ∗
      "R25" ↦ᵣ r25 ∗
      "R26" ↦ᵣ r26 ∗
      "R27" ↦ᵣ r27 ∗
      "R28" ↦ᵣ r28 ∗
      "SP_EL2" ↦ᵣ RVal_Bits sp ∗
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
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗
  instr 0x000000001030003c (Some a3c) -∗
  (* instr 0x0000000010300040 (Some a40) -∗ *)
  instr_pre 0x0000000010300040 (a40_tst_imm_spec) -∗
  instr 0x0000000010300044 (Some a44) -∗
  instr 0x0000000010300048 (Some a48) -∗
  instr 0x000000001030004c (Some a4c) -∗
  (* instr_pre 0x000000001030004c (cmp_R_R_spec 0x000000001030004c "R20" "R23") -∗ *)
  instr 0x0000000010300050 (Some a50) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x000000001030002c binary_search_loop_spec.
Proof.
(*PROOF_START*)
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2)).
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try (rename select (_ ↔ R _ _) into HR; rewrite bv_or_0_l in HR; [|done];
            match type of HR with | (Is_true ?b) ↔ _ => rename b into bres end).
  - bv_solve.
  - bv_solve.
  - bv_solve.
  - bv_solve.
  - bv_simplify_arith_hyp select (ite _ _ _ ≠ ite _ _ _).
    destruct bres; simpl in *; bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct bres; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (_ ≤ i).
    destruct bres; simpl in *; eauto.
    apply: binary_search_cond_2; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct bres; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (ite _ _ _ = ite _ _ _).
    bv_simplify_arith_hyp select (_ ≤ i).
    destruct bres; simpl in *; [solve_goal|].
    apply: binary_search_cond_2; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct bres; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (¬ _ ≤ _).
    bv_simplify_arith_hyp select (_ ≤ i).
    destruct bres; simpl in *; bv_solve.
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
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜bv_unsigned (args !!! 1%nat) `mod` 8 = 0⌝ ∗
    ⌜bv_unsigned (args !!! 1%nat) + (length data) * 8 < 2 ^ 52⌝ ∗
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

  instr 0x0000000010300054 (Some a54) -∗
  instr 0x0000000010300058 (Some a58) -∗
  instr 0x000000001030005c (Some a5c) -∗
  instr 0x0000000010300060 (Some a60) -∗
  instr 0x0000000010300064 (Some a64) -∗
  instr 0x0000000010300068 (Some a68) -∗
  instr 0x000000001030006c (Some a6c) -∗
  instr 0x0000000010300070 (Some a70) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x0000000010300000 (binary_search_spec stack_size).
Proof.
(*PROOF_START*)
  move => ?. iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try rewrite ->@bv_or_0_l in * by done.
  all: try bv_solve.
  - revert select (_ ≠ [BV{64} 0]) => /bv_eq. bv_solve.
  - eauto.
  - eauto.
(*PROOF_END*)
Time Qed.

End proof.
