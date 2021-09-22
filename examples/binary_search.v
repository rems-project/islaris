Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.sys_regs.
Require Import isla.calling_convention.
From isla.instructions.binary_search Require Import instrs.

    Lemma bv_or_0_l n (b1 b2 : bv n) :
      bv_unsigned b1 = 0 →
      bv_or b1 b2 = b2.
    Proof. Admitted.
Lemma bv_signed_eq n (b1 b2 : bv n) :
  b1 = b2 ↔ bv_signed b1 = bv_signed b2.
Proof. split; [naive_solver |]. Admitted.

Lemma bv_1_ind (P : bv 1 → Prop) :
  P [BV{1} 1] → P [BV{1} 0] → ∀ b : bv 1, P b.
Proof.
  move => ???.
Admitted.

Section proof.
Context `{!islaG Σ} `{!threadG}.

(* TODO: allow the function to use the stack? *)
Definition comp_spec (stack_size : Z) (R : bv 64 → bv 64 → Prop) (P : iProp Σ) : iProp Σ :=
  (c_call stack_size (λ args sp RET,
     ∃ x y : bv 64,
     ⌜args !!! 0%nat = RVal_Bits x⌝ ∗
     ⌜args !!! 1%nat = RVal_Bits y⌝ ∗
     P ∗
     RET (λ rets, ∃ b : bool, ⌜rets !!! 0%nat = RVal_Bits (bool_to_bv 64 b)⌝ ∗ ⌜b ↔ R x y⌝ ∗ P ∗ True)
  ))%I.
Typeclasses Opaque comp_spec.
Global Instance : LithiumUnfold (comp_spec) := I.

Definition sub_R_R_R_spec (pc : Z) (R1 R2 R3 : string) : iProp Σ :=
  ∃ (r2 r3 : bv 64),
  R1 ↦ᵣ: λ r1,
  R2 ↦ᵣ RVal_Bits r2 ∗
  R3 ↦ᵣ RVal_Bits r3 ∗
  instr_pre (pc + 4) (
    R1 ↦ᵣ RVal_Bits (bv_sub r2 r3) ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    R3 ↦ᵣ RVal_Bits r3 ∗
    True
  ).
Global Instance : LithiumUnfold (sub_R_R_R_spec) := I.

Lemma a2c_spec :
  instr 0x000000001030002c (Some a2c) -∗
  instr_body 0x000000001030002c (sub_R_R_R_spec 0x000000001030002c "R8" "R20" "R23").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Definition cmp_R_R_spec (pc : Z) (R1 R2 : string) : iProp Σ :=
  ∃ (r1 r2 : bv 64),
  reg_col CNVZ_regs ∗
  R1 ↦ᵣ RVal_Bits r1 ∗
  R2 ↦ᵣ RVal_Bits r2 ∗
  instr_pre (pc + 4) (
    R1 ↦ᵣ RVal_Bits r1 ∗
    R2 ↦ᵣ RVal_Bits r2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits (bv_extract 63 1 (bv_sub r1 r2)) ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (r1 = r2))) ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_unsigned r2 ≤ bv_unsigned r1))) ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits (bool_to_bv 1 (bool_decide (bv_signed (bv_sub r1 r2) ≠ bv_signed r1 - bv_signed r2))) ∗
    True
  ).
Global Instance : LithiumUnfold (cmp_R_R_spec) := I.

Lemma a4c_has_cmp_R_R_spec :
  instr 0x000000001030004c (Some a4c) -∗
  instr_body 0x000000001030004c (cmp_R_R_spec 0x000000001030004c "R20" "R23").
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  - bv_simplify => /=. do 2 f_equal. bv_solve.
  - apply bv_eq. case_bool_decide as Hbv; case_bool_decide as Heq => //; subst; exfalso; contradict Hbv.
    + move/bv_eq in Heq. bv_solve.
    + bv_solve.
  - apply bv_eq. case_bool_decide as Hbv; case_bool_decide => //; exfalso; contradict Hbv; bv_solve.
  - apply bv_eq.
    case_bool_decide as Hbv; case_bool_decide as Heq => //; exfalso; contradict Hbv.
    + apply/bv_signed_eq. bv_simplify_arith.
      bv_simplify_arith_hyp Heq.
      rewrite (bv_wrap_small 128 (bv_unsigned _ + _)); [|bv_solve].
      rewrite (bv_wrap_small 128 (_ + 1)); [|bv_solve].
      rewrite (bv_swrap_small 128 (bv_signed _ + _)); [|bv_solve].
      have -> : bv_swrap 64 (bv_unsigned r1 + bv_wrap 64 (- bv_unsigned r2 - 1) + 1) = bv_swrap 64 (bv_unsigned r1 - bv_unsigned r2) by bv_solve.
      bv_solve.
    + apply/bv_signed_eq. bv_simplify_arith.
      bv_simplify_arith_hyp Heq.
      rewrite (bv_wrap_small 128 (bv_unsigned _ + _)); [|bv_solve].
      rewrite (bv_wrap_small 128 (_ + 1)); [|bv_solve].
      rewrite (bv_swrap_small 128 (bv_signed _ + _)); [|bv_solve].
      rewrite (bv_swrap_small 128 (_ + _)); [|bv_solve].
      rewrite (bv_swrap_small 128 1); [|bv_solve].
      have -> : bv_swrap 64 (bv_unsigned r1 + bv_wrap 64 (- bv_unsigned r2 - 1) + 1)
               = bv_swrap 64 (bv_unsigned r1 - bv_unsigned r2) by bv_solve.
      bv_solve.
Qed.

Definition a40_tst_imm_spec : iProp Σ :=
  ∃ (v : bv 64),
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits v ∗
  instr_pre 0x0000000010300044 (
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
  - admit.
  - bv_simplify.
    rewrite Z.shiftr_eq_0 // ?Z.land_nonneg; [lia|].
    apply: Z.le_lt_trans; [apply Z.log2_land; bv_solve| bv_solve].
  - admit.
Admitted.

Definition a44_csel_spec : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  "R20" ↦ᵣ RVal_Bits v1 ∗
  "R24" ↦ᵣ RVal_Bits v2 ∗
  instr_pre 0x0000000010300048 (
    "R20" ↦ᵣ RVal_Bits (ite (bool_decide (bv_unsigned pstatez = 0)) v1 v2) ∗
    "R24" ↦ᵣ RVal_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
    True
  ).
Global Instance : LithiumUnfold (a44_csel_spec) := I.

Lemma a44_has_csel_spec :
  instr 0x0000000010300044 (Some a44) -∗
  instr_body 0x0000000010300044 (a44_csel_spec).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - rewrite bool_decide_true //. by destruct pstatez using bv_1_ind.
Qed.

Definition a48_csinc_spec : iProp Σ :=
  ∃ (v1 v2 : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
  "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
  "R23" ↦ᵣ RVal_Bits v1 ∗
  "R24" ↦ᵣ RVal_Bits v2 ∗
  instr_pre 0x000000001030004c (
    "R23" ↦ᵣ RVal_Bits (ite (bool_decide (bv_unsigned pstatez = 1)) v1 (bv_add_Z v2 1)) ∗
    "R24" ↦ᵣ RVal_Bits v2 ∗
    "PSTATE" # "N" ↦ᵣ RVal_Bits pstaten ∗
    "PSTATE" # "Z" ↦ᵣ RVal_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ RVal_Bits pstatec ∗
    "PSTATE" # "V" ↦ᵣ RVal_Bits pstatev ∗
    True
  ).
Global Instance : LithiumUnfold (a48_csinc_spec) := I.

Lemma a48_has_csinc_spec :
  instr 0x0000000010300048 (Some a48) -∗
  instr_body 0x0000000010300048 (a48_csinc_spec).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - rewrite bool_decide_false //=. by destruct pstatez using bv_1_ind.
Qed.


Definition binary_search_loop_spec : iProp Σ :=
  ∃ (x l r comp xs tmp2 sp : bv 64) (data : list (bv 64)),
  ∃ stack_size R P,
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R25"; "R26"; "R27"; "R28"; "R29"; "R30" ]) ∗
  "R19" ↦ᵣ RVal_Bits x ∗
  "R20" ↦ᵣ RVal_Bits r ∗
  "R21" ↦ᵣ RVal_Bits xs ∗
  "R22" ↦ᵣ RVal_Bits comp ∗
  "R23" ↦ᵣ RVal_Bits l ∗
  "R24" ↦ᵣ RVal_Bits tmp2 ∗
  "SP_EL2" ↦ᵣ RVal_Bits sp ∗
  xs ↦ₘ∗ data ∗
  □ instr_pre (bv_unsigned comp) (comp_spec stack_size R P) ∗
  P ∗
  ⌜stack_size < bv_unsigned sp < 2 ^ 52⌝ ∗
  bv_sub_Z sp stack_size ↦ₘ? stack_size ∗
  ⌜bv_unsigned l < bv_unsigned r ≤ length data⌝ ∗
  ⌜bv_unsigned xs + (length data) * 8 < 2 ^ 52⌝ ∗
  ⌜StronglySorted R data⌝ ∗ ⌜Transitive R⌝ ∗
  ⌜∀ (i : nat) y, i < bv_unsigned l → data !! i = Some y → R y x⌝ ∗
  ⌜∀ (i : nat) y, bv_unsigned r ≤ i → data !! i = Some y → ¬ R y x⌝ ∗
  instr_pre 0x0000000010300054 (
    ∃ (l' r' tmp2 : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      reg_col ((λ r, (RegColDirect r, None)) <$> ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7"; "R8"; "R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R25"; "R26"; "R27"; "R28"; "R29"; "R30" ]) ∗
      "R19" ↦ᵣ RVal_Bits x ∗
      "R20" ↦ᵣ RVal_Bits r' ∗
      "R21" ↦ᵣ RVal_Bits xs ∗
      "R22" ↦ᵣ RVal_Bits comp ∗
      "R23" ↦ᵣ RVal_Bits l' ∗
      "R24" ↦ᵣ RVal_Bits tmp2 ∗
      "SP_EL2" ↦ᵣ RVal_Bits sp ∗
      xs ↦ₘ∗ data ∗
      P ∗
      bv_sub_Z sp stack_size ↦ₘ? stack_size ∗
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


Lemma binary_search_loop :
  (* instr 0x000000001030002c (Some a2c) -∗ *)
  instr_body 0x000000001030002c (sub_R_R_R_spec 0x000000001030002c "R8" "R20" "R23") -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗
  instr 0x000000001030003c (Some a3c) -∗
  (* instr 0x0000000010300040 (Some a40) -∗ *)
  instr_pre 0x0000000010300040 (a40_tst_imm_spec) -∗
  (* instr 0x0000000010300044 (Some a44) -∗ *)
  instr_pre 0x0000000010300044 (a44_csel_spec) -∗
  (* instr 0x0000000010300048 (Some a48) -∗ *)
  instr_pre 0x0000000010300048 (a48_csinc_spec) -∗
  (* instr 0x000000001030004c (Some a4c) -∗ *)
  instr_pre 0x000000001030004c (cmp_R_R_spec 0x000000001030004c "R20" "R23") -∗
  instr 0x0000000010300050 (Some a50) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x000000001030002c binary_search_loop_spec.
Proof.
(* Admitted. *)
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2)).
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try (rename select (_ ↔ R _ _) into HR; rewrite bv_or_0_l in HR; [|done]).
  - bv_simplify => /=.
    have -> : (bv_wrap 64 (bv_unsigned l) + bv_wrap 64 (bv_wrap 64 (bv_unsigned r - bv_unsigned l) ≫ 1))
             = (bv_unsigned l + (bv_unsigned r - bv_unsigned l) `div` 2) by bv_solve.
    rewrite (bv_wrap_small 61 _); [|bv_solve].
    bv_solve.
  - bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct b; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (¬ _ ≤ _).
    bv_simplify_arith_hyp select (_ ≤ i).
    destruct b; simpl in *; bv_solve.
  - bv_simplify_arith_hyp select (ite _ _ _ ≠ ite _ _ _).
    destruct b; simpl in *; bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct b; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (_ ≤ i).
    destruct b; simpl in *; eauto.
    apply: binary_search_cond_2; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (i < _).
    destruct b; simpl in *; eauto.
    apply: binary_search_cond_1; [solve_goal..|].
    bv_solve.
  - bv_simplify_arith_hyp select (ite _ _ _ = ite _ _ _).
    bv_simplify_arith_hyp select (_ ≤ i).
    destruct b; simpl in *; [solve_goal|].
    apply: binary_search_cond_2; [solve_goal..|].
    bv_solve.
Time Qed.


Lemma binary_search stack_size :
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
  instr_body 0x0000000010300000 (c_call (stack_size + 64) (λ args sp RET,
     RET (λ rets, ∃ r : bv 64, ⌜rets !!! 0%nat = RVal_Bits r⌝))
  ).
Proof.
  iStartProof.
Admitted.

(*
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  - do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    + admit.
    + done.
  - do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    do 100 liAStep; liShow.
    repeat liAStep; liShow.

Abort.
*)
End proof.
