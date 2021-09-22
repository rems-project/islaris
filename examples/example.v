Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.sys_regs.
From isla.instructions.example Require Import instrs.

(*
C:
int test() {
    return 0;
}
compiled via GCC:
        mov     w0, 0
        ret
 *)

Definition start_address := [BV{64} (0x0000000010300000 - 0x4)].
Definition test_state_local := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "_PC" := RVal_Bits start_address ]> $
    <[ "__PC_changed" := RVal_Bool false ]> $
    <[ "R30" := RegVal_Poison ]> $
    <[ "R1" := RegVal_Poison ]> $
    <[ "R0" := RegVal_Poison ]> $
    <[ "R27" := RVal_Bits [BV{64} 0x101f1000] ]> $
    <[ "R28" := RegVal_Poison ]> $
     sys_regs_map;
  seq_nb_state  := false;
|}.

Definition test_state_global := {|
    seq_instrs :=
    <[ [BV{64} 0x0000000010300000] := a0]> $
    <[ [BV{64} 0x0000000010300004] := a4]> $
    <[ [BV{64} 0x0000000010300008] := a8]> $

    <[ [BV{64} 0x0000000010300010] := a10]> $
    <[ [BV{64} 0x0000000010300014] := a14]> $
    ∅;
    seq_mem := ∅
|}.


Definition test_state_spec : list seq_label := [
  SWriteMem [BV{64} 0x101f1000] [BV{64} 0];
  SInstrTrap ([BV{64} 0x000000001030000c])
].

Lemma test_state_iris `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c None -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  reg_col sys_regs -∗
  "_PC" ↦ᵣ RVal_Bits start_address -∗
  "__PC_changed" ↦ᵣ RVal_Bool false -∗
  "R30" ↦ᵣ RegVal_Poison -∗
  "R1" ↦ᵣ RegVal_Poison -∗
  "R0" ↦ᵣ RegVal_Poison -∗
  "R27" ↦ᵣ RVal_Bits [BV{64} 0x101f1000] -∗
  "R28" ↦ᵣ RegVal_Poison -∗
  mmio_range [BV{64} 0x101f1000] 8 -∗
  spec_trace test_state_spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma test_state_adequate κs t2 σ2 n:
  nsteps n (initial_local_state <$> [test_state_local.(seq_regs)],
            test_state_global) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
  κs `prefix_of` test_state_spec.
Proof.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  iIntros (?) "#Hi #Hbm Hspec /= !>". iSplitL => //.
  iIntros (?).
  do 7 (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(?&?&?&?&?&?&?&Hregs)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hctx".
  iMod (sys_regs_init with "Hctx Hregs") as "(?&?&?)". iModIntro. iFrame.
  iApply (test_state_iris with "[] [] [] [] [] [] [$] [$] [$] [$] [$] [$] [$] [$] [] [$]").
  all: try by unshelve iApply (instr_intro with "Hi").
  all: try by iApply (mmio_range_intro with "[//]").
Qed.

Definition test_state_fn1_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (r : addr) v0,
    reg_col sys_regs ∗
    "R0" ↦ᵣ v0 ∗
    "R30" ↦ᵣ RVal_Bits r ∗
    instr_pre (bv_unsigned r) (
      reg_col sys_regs ∗
      "R30" ↦ᵣ RVal_Bits r ∗
      "R0" ↦ᵣ RVal_Bits [BV{64} 0] ∗ True
    ).
Arguments test_state_fn1_spec /.

Lemma test_state_iris_fn1 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr_body 0x0000000010300010 test_state_fn1_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.

Definition test_state_fn2_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  reg_col sys_regs ∗
  "R30" ↦ᵣ RegVal_Poison ∗
  "R1" ↦ᵣ RegVal_Poison ∗
  "R0" ↦ᵣ RegVal_Poison ∗
  "R27" ↦ᵣ RVal_Bits [BV{64} 0x101f1000] ∗
  mmio_range [BV{64} 0x101f1000] 8 ∗
  "R28" ↦ᵣ RegVal_Poison ∗
  spec_trace test_state_spec.
Arguments test_state_fn2_spec /.

Lemma test_state_iris_fn2 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c None -∗
  □ instr_pre 0x0000000010300010 test_state_fn1_spec -∗
  instr_body 0x0000000010300000 test_state_fn2_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.

Lemma test_state_adequate' κs t2 σ2 n:
  nsteps n (initial_local_state <$> [test_state_local.(seq_regs)],
            test_state_global) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
  κs `prefix_of` test_state_spec.
Proof.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  iIntros (?) "#Hi #Hbm Hspec /= !>". iSplitL => //.
  iIntros (?) "/=".
  do 7 (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(HPC&Hchanged&?&?&?&?&?&Hregs)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hctx".
  iMod (sys_regs_init with "Hctx Hregs") as "(?&?&?)". iModIntro. iFrame.

  iAssert (
      □ instr_body 0x0000000010300000 test_state_fn2_spec ∗
      □ instr_body 0x0000000010300010 test_state_fn1_spec
    )%I as "(Hmain & _)". {
    iLöb as "IH". iDestruct "IH" as "(?&?)".
    (repeat iSplit); iModIntro.
    - iApply test_state_iris_fn2.
      all: try by unshelve iApply (instr_intro with "Hi").
      iModIntro.
      iApply instr_pre_to_body. by iModIntro.
    - iApply test_state_iris_fn1.
      all: try by unshelve iApply (instr_intro with "Hi").
  }
  iApply (wp_next_instr_pre with "Hmain [HPC Hchanged]").
  - iExists _, _, _. by iFrame.
  - iFrame. by iApply (mmio_range_intro with "[//]").
Qed.

(*
0x0000000010300018: cmp x1, 0
0x000000001030001c: bne 0xc  --\
0x0000000010300020: mov x0, 1  |
0x0000000010300024: b   0x8  --|--\
0x0000000010300028: bl  34<-/  |
0x000000001030002c: mov OUT, x0 <-/


0x0000000010300034: mov x0, 0
0x0000000010300038: ret
*)

Definition test_state2_local (n1 : Z) Hin := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "R1" := RVal_Bits (BV 64 n1 Hin) ]> $
    <[ "_PC" := RVal_Bits start_address ]> $
    <[ "__PC_changed" := RVal_Bool false ]> $
    sys_regs_map;
  seq_nb_state  := false;
|}.
Definition test_state2_global  := {|
  seq_instrs :=
    <[[BV{64} 0x0000000010300018] := a18]> $
    <[[BV{64} 0x000000001030001c] := a1c ]> $
    <[[BV{64} 0x0000000010300020] := a20]> $
    <[[BV{64} 0x0000000010300024] := a24]> $
    <[[BV{64} 0x0000000010300028] := a28]> $
    <[[BV{64} 0x000000001030002c] := a2c]> $

    <[[BV{64} 0x0000000010300034] := a34]> $
    <[[BV{64} 0x0000000010300038] := a38]> $
    ∅;
  seq_mem := ∅
|}.

Definition test_state2_spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300030] ].

Lemma test_state2_iris `{!islaG Σ} `{!threadG} n1 Hin :
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c ) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 None -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗

  reg_col sys_regs -∗
  "_PC" ↦ᵣ RVal_Bits [BV{64} (0x0000000010300018 - 0x4)] -∗
  "__PC_changed" ↦ᵣ RVal_Bool false -∗
  "R30" ↦ᵣ RegVal_Poison -∗
  "R1" ↦ᵣ RVal_Bits (BV 64 n1 Hin) -∗
  "R0" ↦ᵣ RegVal_Poison -∗
  "R28" ↦ᵣ RegVal_Poison -∗
  "PSTATE" # "N" ↦ᵣ RVal_Bits [BV{1} 0] -∗
  "PSTATE" # "Z" ↦ᵣ RVal_Bits [BV{1} 0] -∗
  "PSTATE" # "C" ↦ᵣ RVal_Bits [BV{1} 0] -∗
  "PSTATE" # "V" ↦ᵣ RVal_Bits [BV{1} 0] -∗
  spec_trace test_state2_spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.
