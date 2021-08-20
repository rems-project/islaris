Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.examples.sys_regs.
From isla.instructions Require Import bl_0x100 mov_w0_0 ret mov_x28_x0 mov_x0_1 b_0x8 cmp_x1_0 str_x28_x27.

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
    <[ "_PC" := Val_Bits start_address ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
    <[ "R30" := Val_Poison ]> $
    <[ "R1" := Val_Poison ]> $
    <[ "R0" := Val_Poison ]> $
    <[ "R27" := Val_Bits [BV{64} 0x101f1000] ]> $
    <[ "R28" := Val_Poison ]> $
     sys_regs_map;
  seq_nb_state  := false;
|}.

Definition test_state_global := {|
    seq_instrs :=
    <[ [BV{64} 0x0000000010300000] := [bl_0x100_trace]]> $    (* bl 0x100 *)
    <[ [BV{64} 0x0000000010300004] := [mov_x28_x0_trace]]> $  (* mov OUT, x0 *)
    <[ [BV{64} 0x0000000010300008] := [str_x28_x27_trace]]> $ (* str x28, [x27] *)
    <[ [BV{64} 0x0000000010300100] := [mov_w0_0_trace]]> $    (* mov w0, 0 *)
    <[ [BV{64} 0x0000000010300104] := [ret_trace]]> $         (* ret *)
    ∅;
    seq_mem := ∅
|}.


Definition test_state_spec : list seq_label := [
  SWriteMem [BV{64} 0x101f1000] [BV{64} 0];
  SInstrTrap ([BV{64} 0x000000001030000c])
].

Lemma test_state_iris `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some [bl_0x100_trace]) -∗
  instr 0x0000000010300004 (Some [mov_x28_x0_trace]) -∗
  instr 0x0000000010300008 (Some [str_x28_x27_trace]) -∗
  instr 0x000000001030000c None -∗
  instr 0x0000000010300100 (Some [mov_w0_0_trace]) -∗
  instr 0x0000000010300104 (Some [ret_trace]) -∗
  reg_col sys_regs -∗
  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R30" ↦ᵣ Val_Poison -∗
  "R1" ↦ᵣ Val_Poison -∗
  "R0" ↦ᵣ Val_Poison -∗
  "R27" ↦ᵣ Val_Bits [BV{64} 0x101f1000] -∗
  "R28" ↦ᵣ Val_Poison -∗
  mmio_range [BV{64} 0x101f1000] 8 -∗
  spec_trace test_state_spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.

  Unshelve. all: unLET; normalize_and_simpl_goal => //=.
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
    "R30" ↦ᵣ Val_Bits r ∗
    instr_pre (bv_unsigned r) (
      reg_col sys_regs ∗
      "R30" ↦ᵣ Val_Bits r ∗
      "R0" ↦ᵣ Val_Bits [BV{64} 0] ∗ True
    ).
Arguments test_state_fn1_spec /.

Lemma test_state_iris_fn1 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300100 (Some [mov_w0_0_trace]) -∗
  instr 0x0000000010300104 (Some [ret_trace]) -∗
  instr_body 0x0000000010300100 test_state_fn1_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.

Definition test_state_fn2_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  reg_col sys_regs ∗
  "R30" ↦ᵣ Val_Poison ∗
  "R1" ↦ᵣ Val_Poison ∗
  "R0" ↦ᵣ Val_Poison ∗
  "R27" ↦ᵣ Val_Bits [BV{64} 0x101f1000] ∗
  mmio_range [BV{64} 0x101f1000] 8 ∗
  "R28" ↦ᵣ Val_Poison ∗
  spec_trace test_state_spec.
Arguments test_state_fn2_spec /.

Lemma test_state_iris_fn2 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some [bl_0x100_trace]) -∗
  instr 0x0000000010300004 (Some [mov_x28_x0_trace]) -∗
  instr 0x0000000010300008 (Some [str_x28_x27_trace]) -∗
  instr 0x000000001030000c None -∗
  □ instr_pre 0x0000000010300100 test_state_fn1_spec -∗
  instr_body 0x0000000010300000 test_state_fn2_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: unLET; normalize_and_simpl_goal => //=.
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
      □ instr_body 0x0000000010300100 test_state_fn1_spec
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

(* trace of bne 0xc: (at address 0x0000000010300004)
  (* TODO: Can we somehoe merge the common parts of the two traces? *)

(trace
  (declare-const v12 (_ BitVec 4))
  (declare-const v14 (_ BitVec 1))
  (declare-const v15 (_ BitVec 1))
  (declare-const v16 (_ BitVec 5))
  (declare-const v17 (_ BitVec 1))
  (declare-const v20 (_ BitVec 1))
  (declare-const v24 (_ BitVec 2))
  (declare-const v25 (_ BitVec 1))
  (declare-const v27 (_ BitVec 1))
  (declare-const v28 (_ BitVec 8))
  (declare-const v29 (_ BitVec 1))
  (declare-const v30 (_ BitVec 1))
  (declare-const v31 (_ BitVec 1))
  (declare-const v32 (_ BitVec 1))
  (declare-const v33 (_ BitVec 1))
  (declare-const v35 (_ BitVec 1))
  (declare-const v114 (_ BitVec 32))
  (read-reg |PSTATE| ((_ field |Z|)) (_ struct (|F| #b1) (|GE| v12) (|A| #b1) (|C| v15) (|Z| v35) (|UAO| v33) (|D| #b1) (|BTYPE| v24) (|V| v17) (|N| v25) (|PAN| v29) (|TCO| v32) (|I| #b1) (|SS| #b0) (|SP| #b1) (|Q| v14) (|nRW| #b0) (|T| v31) (|M| v16) (|EL| #b00) (|J| v20) (|DIT| #b0) (|SSBS| v30) (|IL| #b0) (|IT| v28) (|E| v27)))
  (define-const v3435 (not (= v35 #b1)))
  (branch 0 "model/aarch64.sail 12127:4 - 12129:5")
  (assert v3435)
  (read-reg |_PC| nil #x0000000010300004)
  (write-reg |_PC| nil #x0000000010300010)
  (write-reg |__PC_changed| nil true))
(trace
  (declare-const v12 (_ BitVec 4))
  (declare-const v14 (_ BitVec 1))
  (declare-const v15 (_ BitVec 1))
  (declare-const v16 (_ BitVec 5))
  (declare-const v17 (_ BitVec 1))
  (declare-const v20 (_ BitVec 1))
  (declare-const v24 (_ BitVec 2))
  (declare-const v25 (_ BitVec 1))
  (declare-const v27 (_ BitVec 1))
  (declare-const v28 (_ BitVec 8))
  (declare-const v29 (_ BitVec 1))
  (declare-const v30 (_ BitVec 1))
  (declare-const v31 (_ BitVec 1))
  (declare-const v32 (_ BitVec 1))
  (declare-const v33 (_ BitVec 1))
  (declare-const v35 (_ BitVec 1))
  (read-reg |PSTATE| ((_ field |Z|)) (_ struct (|F| #b1) (|GE| v12) (|A| #b1) (|C| v15) (|Z| v35) (|UAO| v33) (|D| #b1) (|BTYPE| v24) (|V| v17) (|N| v25) (|PAN| v29) (|TCO| v32) (|I| #b1) (|SS| #b0) (|SP| #b1) (|Q| v14) (|nRW| #b0) (|T| v31) (|M| v16) (|EL| #b00) (|J| v20) (|DIT| #b0) (|SSBS| v30) (|IL| #b0) (|IT| v28) (|E| v27)))
  (define-const v3435 (not (= v35 #b1)))
  (branch 0 "model/aarch64.sail 12127:4 - 12129:5")
  (assert (not v3435)))

*)
Definition trc_bne_0xc : list trc := [
[
  Smt (DeclareConst 35 (Ty_BitVec 1)) Mk_annot;
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [ ("Z", (Val_Symbolic 35)) ]) Mk_annot;
  Smt (DefineConst 3435 (Unop Not (Binop Eq (Val (Val_Symbolic 35) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Val (Val_Symbolic (3435)) Mk_annot)) Mk_annot;
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300004]) Mk_annot;
  WriteReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300010]) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
]; [
  Smt (DeclareConst 35 (Ty_BitVec 1)) Mk_annot;
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [ ("Z", (Val_Symbolic 35)) ]) Mk_annot;
  Smt (DefineConst 3435 (Unop Not (Binop Eq (Val (Val_Symbolic 35) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Unop Not (Val (Val_Symbolic (3435)) Mk_annot) Mk_annot)) Mk_annot
]
].

(*
0x0000000010300000: cmp x1, 0
0x0000000010300004: bne 0xc  --\
0x0000000010300008: mov x0, 1  |
0x000000001030000c: b   0x8  --|--\
0x0000000010300010: bl  0x100<-/  |
0x0000000010300014: mov OUT, x0 <-/


0x0000000010300110: mov x0, 0
0x0000000010300114: ret
*)

Definition test_state2_local (n1 : Z) Hin := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "R1" := Val_Bits (BV 64 n1 Hin) ]> $
    <[ "_PC" := Val_Bits start_address ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
    sys_regs_map;
  seq_nb_state  := false;
|}.
Definition test_state2_global  := {|
  seq_instrs :=
    <[[BV{64} 0x0000000010300000] := [cmp_x1_0_trace]]> $
    <[[BV{64} 0x0000000010300004] := trc_bne_0xc ]> $
    <[[BV{64} 0x0000000010300008] := [mov_x0_1_trace]]> $
    <[[BV{64} 0x000000001030000c] := [b_0x8_trace]]> $
    <[[BV{64} 0x0000000010300010] := [bl_0x100_trace]]> $
    <[[BV{64} 0x0000000010300014] := [mov_x28_x0_trace]]> $

    <[[BV{64} 0x0000000010300110] := [mov_w0_0_trace]]> $
    <[[BV{64} 0x0000000010300114] := [ret_trace]]> $
    ∅;
  seq_mem := ∅
|}.

Definition test_state2_spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300018] ].

Lemma test_state2_iris `{!islaG Σ} `{!threadG} n1 Hin :
  instr 0x0000000010300000 (Some [cmp_x1_0_trace]) -∗
  instr 0x0000000010300004 (Some trc_bne_0xc ) -∗
  instr 0x0000000010300008 (Some [mov_x0_1_trace]) -∗
  instr 0x000000001030000c (Some [b_0x8_trace]) -∗
  instr 0x0000000010300010 (Some [bl_0x100_trace]) -∗
  instr 0x0000000010300014 (Some [mov_x28_x0_trace]) -∗
  instr 0x0000000010300018 None -∗
  instr 0x0000000010300110 (Some [mov_w0_0_trace]) -∗
  instr 0x0000000010300114 (Some [ret_trace]) -∗

  reg_col sys_regs -∗
  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R30" ↦ᵣ Val_Poison -∗
  "R1" ↦ᵣ Val_Bits (BV 64 n1 Hin) -∗
  "R0" ↦ᵣ Val_Poison -∗
  "R28" ↦ᵣ Val_Poison -∗
  "PSTATE" # "N" ↦ᵣ Val_Bits [BV{1} 0] -∗
  "PSTATE" # "Z" ↦ᵣ Val_Bits [BV{1} 0] -∗
  "PSTATE" # "C" ↦ᵣ Val_Bits [BV{1} 0] -∗
  "PSTATE" # "V" ↦ᵣ Val_Bits [BV{1} 0] -∗
  spec_trace test_state2_spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.
