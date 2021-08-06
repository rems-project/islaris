Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
From isla.instructions Require Import load.


(* Ltac solve_trace_step := by econstructor. *)
(* Ltac do_trace_step := *)
(*   apply: TraceStep'; [solve_trace_step | done |]; simpl. *)


(* trace of add x1, x2, x3:
  (declare-const v3359 (_ BitVec 64))
  (declare-const v3361 (_ BitVec 64))
  (read-reg |R2| nil v3359)
  (define-const v3425 v3359)
  (read-reg |R3| nil v3361)
  (define-const v3426 v3361)
  (define-const v3431 ((_ zero_extend 64) v3425))
  (define-const v3432 ((_ zero_extend 64) v3426))
  (define-const v3433 (bvadd v3431 v3432))
  (define-const v3437 ((_ extract 63 0) v3433))
  (define-const v3452 v3437)
  (write-reg |R1| nil v3452)
*)
Definition trc_add_x1_x2_x3 : trc :=
  [
  Smt (DeclareConst 3359 (Ty_BitVec 64)) Mk_annot;
  Smt (DeclareConst 3361 (Ty_BitVec 64)) Mk_annot;
  ReadReg "R2" [] (Val_Symbolic 3359) Mk_annot;
  Smt (DefineConst 3425 (Val (Val_Symbolic 3359) Mk_annot)) Mk_annot;
  ReadReg "R3" [] (Val_Symbolic 3361) Mk_annot;
  Smt (DefineConst 3426 (Val (Val_Symbolic 3361) Mk_annot)) Mk_annot;
  Smt (DefineConst 3431 (Unop (ZeroExtend 64) (Val (Val_Symbolic 3425) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3432 (Unop (ZeroExtend 64) (Val (Val_Symbolic 3426) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3433 (Manyop (Bvmanyarith Bvadd) [Val (Val_Symbolic 3431) Mk_annot; Val (Val_Symbolic 3432) Mk_annot] Mk_annot)) Mk_annot;
  Smt (DefineConst 3437 (Unop (Extract 63 0) (Val (Val_Symbolic 3433) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3452 (Val (Val_Symbolic 3437) Mk_annot)) Mk_annot;
  WriteReg "R1" [] (Val_Symbolic 3452) Mk_annot
].

(*
C:
int test() {
    return 0;
}
compiled via GCC:
        mov     w0, 0
        ret

trace of mov w0, 0:
  (write-reg |R0| nil #x0000000000000000))

trace of ret:
(trace
  (declare-const v3428 (_ BitVec 64))
  (define-const v3429 v3428)
  (read-reg |R30| nil v3429)
  (define-const v3435 v3429)
#  (write-reg |BTypeNext| nil #b00)
  (define-const v3436 v3435)
  (branch-address v3436)
  (define-const v3437 v3435)
# There are two generated traces, but they seem to do the same
#  (define-const v3471 (= (bvor #b0 ((_ extract 0 0) (bvlshr v3437 #x0000000000000037))) #b1))
#  (branch 0 "model/aarch_mem.sail 6170:20 - 6170:81")
#  (assert v3471)
  (write-reg |_PC| nil v3437)
  (write-reg |__PC_changed| nil true))
*)

Definition trc_mov_w0_0 : trc := [
   WriteReg "R0" [] (Val_Bits [BV{64} 0x0000000000000000]) Mk_annot
  ].

Definition trc_mov_x0_1 : trc := [
   WriteReg "R0" [] (Val_Bits [BV{64} 0x0000000000000001]) Mk_annot
  ].

Definition trc_ret : trc := [
  Smt (DeclareConst 3428 (Ty_BitVec 64)) Mk_annot;
  Smt (DefineConst 3429 (Val (Val_Symbolic 3428) Mk_annot)) Mk_annot;
  ReadReg "R30" nil (Val_Symbolic 3429) Mk_annot;
  Smt (DefineConst 3435 (Val (Val_Symbolic 3429) Mk_annot)) Mk_annot;
  (* WriteReg "BTypeNext" nil (Val_Bits 0) Mk_annot; *)
  Smt (DefineConst 3436 (Val (Val_Symbolic 3435) Mk_annot)) Mk_annot;
  BranchAddress (Val_Symbolic 3436) Mk_annot;
  Smt (DefineConst 3437 (Val (Val_Symbolic 3435) Mk_annot)) Mk_annot;
  WriteReg "_PC" nil (Val_Symbolic 3437) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
].

(* trace of bl 0x100: (at address 0x0000000010300000)
(trace
  (read-reg |_PC| nil #x0000000010300000)
  (write-reg |R30| nil #x0000000010300004)
  (read-reg |_PC| nil #x0000000010300000)
  (branch-address #x0000000010300100)
  (write-reg |_PC| nil #x0000000010300100)
  (write-reg |__PC_changed| nil true))
*)
Definition trc_bl_0x100 : trc := [
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300000]) Mk_annot;
  WriteReg "R30" nil (Val_Bits [BV{64} 0x0000000010300004]) Mk_annot;
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300000]) Mk_annot;
  BranchAddress (Val_Bits [BV{64} 0x0000000010300100]) Mk_annot;
  WriteReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300100]) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
].

(* trace of mov x28, x0:
trace
  (declare-const v3368 (_ BitVec 64))
  (define-const v3369 v3368)
  (read-reg |R0| nil v3369)
  (define-const v3450 (bvor #x0000000000000000 v3369))
  (write-reg |R28| nil v3450))
*)
Definition trc_mov_OUT_x0 : trc := [
  Smt (DeclareConst 3368 (Ty_BitVec 64)) Mk_annot;
  Smt (DefineConst 3369 (Val (Val_Symbolic 3368) Mk_annot)) Mk_annot;
  ReadReg "R0" nil (Val_Symbolic 3369) Mk_annot;
  Smt (DefineConst 3450 (Manyop (Bvmanyarith Bvor) [Val (Val_Bits [BV{64} 0x0000000000000000]) Mk_annot; Val (Val_Symbolic 3369) Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "OUT" nil (Val_Symbolic 3450) Mk_annot
].


Definition start_address := [BV{64} (0x0000000010300000 - 0x4)].
Definition test_state_local := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "_PC" := Val_Bits start_address ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
    <[ "R30" := Val_Poison ]> $
    <[ "R1" := Val_Poison ]> $
    <[ "R0" := Val_Poison ]> $
    <[ "OUT" := Val_Poison ]> $
     ∅;
  seq_nb_state  := false;
|}.

Definition test_state_global := {|
    seq_instrs :=
    <[ [BV{64} 0x0000000010300000] := [trc_bl_0x100]]> $   (* bl 0x100: (at address 0x0000000010300000 *)
    <[ [BV{64} 0x0000000010300004] := [trc_mov_OUT_x0]]> $ (* mov OUT, x0 *)
    <[ [BV{64} 0x0000000010300100] := [trc_mov_w0_0]]> $   (* mov w0, 0 *)
    <[ [BV{64} 0x0000000010300104] := [trc_ret]]> $        (* ret *)
    ∅;
    seq_mem := ∅
|}.


Definition test_state_spec : list seq_label := [ SInstrTrap ([BV{64} 0x0000000010300008]) ].

Lemma test_state_iris `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some [trc_bl_0x100]) -∗
  instr 0x0000000010300004 (Some [trc_mov_OUT_x0]) -∗
  instr 0x0000000010300008 None -∗
  instr 0x0000000010300100 (Some [trc_mov_w0_0]) -∗
  instr 0x0000000010300104 (Some [trc_ret]) -∗
  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R30" ↦ᵣ Val_Poison -∗
  "R1" ↦ᵣ Val_Poison -∗
  "R0" ↦ᵣ Val_Poison -∗
  "OUT" ↦ᵣ Val_Poison -∗
  spec_trace test_state_spec -∗
  WPasm [].
Proof.
  iStartProof.
  repeat liAStep; liShow.
Qed.

Lemma test_state_adequate κs t2 σ2 n:
  nsteps n (initial_local_state <$> [test_state_local.(seq_regs)],
            test_state_global) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
  κs `prefix_of` test_state_spec.
Proof.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  iIntros (?) "#Hi Hspec /= !>". iSplitL => //.
  iIntros (?) "/=".
  do 6 rewrite big_sepM_insert //=.
  iIntros "(?&?&?&?&?&?&?)".
  iApply (test_state_iris with "[] [] [] [] [] [$] [$] [$] [$] [$] [$] [$]").
  all: try by unshelve iApply (instr_intro with "Hi").
Qed.

Definition test_state_fn1_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (r : addr) v0,
    "R0" ↦ᵣ v0 ∗
    "R30" ↦ᵣ Val_Bits r ∗
    instr_pre (bv_unsigned r) (
      "R30" ↦ᵣ Val_Bits r ∗
      "R0" ↦ᵣ Val_Bits [BV{64} 0] ∗ True
    ).
Arguments test_state_fn1_spec /.

Lemma test_state_iris_fn1 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300100 (Some [trc_mov_w0_0]) -∗
  instr 0x0000000010300104 (Some [trc_ret]) -∗
  instr_body 0x0000000010300100 test_state_fn1_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve.
  all: done.
Qed.

Definition test_state_fn2_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  "R30" ↦ᵣ Val_Poison ∗
  "R1" ↦ᵣ Val_Poison ∗
  "R0" ↦ᵣ Val_Poison ∗
  "OUT" ↦ᵣ Val_Poison ∗
  spec_trace test_state_spec.
Arguments test_state_fn2_spec /.

Lemma test_state_iris_fn2 `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some [trc_bl_0x100]) -∗
  instr 0x0000000010300004 (Some [trc_mov_OUT_x0]) -∗
  instr 0x0000000010300008 None -∗
  □ instr_pre 0x0000000010300100 test_state_fn1_spec -∗
  instr_body 0x0000000010300000 test_state_fn2_spec.
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve.
  all: done.
Qed.

Lemma test_state_adequate' κs t2 σ2 n:
  nsteps n (initial_local_state <$> [test_state_local.(seq_regs)],
            test_state_global) κs (t2, σ2) →
  (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
  κs `prefix_of` test_state_spec.
Proof.
  set Σ : gFunctors := #[islaΣ].
  apply: (isla_adequacy Σ) => //.
  iIntros (?) "#Hi Hspec /= !>". iSplitL => //.
  iIntros (?) "/=".
  do 6 rewrite big_sepM_insert //=.
  iIntros "(HPC&Hchanged&?&?&?&?&?)".

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
  - iFrame.
Qed.


(* trace of cmp x1, 0:
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3435 v3371)
  (define-const v3440 (bvadd (bvadd ((_ zero_extend 64) v3435) #x0000000000000000ffffffffffffffff) #x00000000000000000000000000000001))
  (define-const v3444 ((_ extract 63 0) v3440))
  (define-const v3457 (concat (concat (concat (bvor (bvand #b0 (bvnot #b1)) ((_ extract 0 0) (bvlshr v3444 ((_ extract 63 0) #x0000000000000000000000000000003f)))) (ite (= v3444 #x0000000000000000) #b1 #b0)) (ite (= ((_ zero_extend 64) v3444) v3440) #b0 #b1)) (ite (= ((_ sign_extend 64) v3444) (bvadd (bvadd ((_ sign_extend 64) v3435) #xffffffffffffffffffffffffffffffff) #x00000000000000000000000000000001)) #b0 #b1)))
  (define-const v3459 ((_ extract 3 3) v3457))
  (read-reg |PSTATE| ((_ field |N|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v20) (|SP| #b1) (|N| v29) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v15) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (write-reg |PSTATE| ((_ field |N|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v20) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v15) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (define-const v3460 ((_ extract 2 2) v3457))
  (read-reg |PSTATE| ((_ field |Z|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v20) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v15) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (write-reg |PSTATE| ((_ field |Z|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v20) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v3460) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (define-const v3461 ((_ extract 1 1) v3457))
  (read-reg |PSTATE| ((_ field |C|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v20) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v3460) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (write-reg |PSTATE| ((_ field |C|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v3461) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v3460) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (define-const v3462 ((_ extract 0 0) v3457))
  (read-reg |PSTATE| ((_ field |V|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v3461) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v3460) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v25) (|DIT| #b0)))
  (write-reg |PSTATE| ((_ field |V|)) (_ struct (|GE| v27) (|F| #b1) (|UAO| v23) (|C| v3461) (|SP| #b1) (|N| v3459) (|Q| v21) (|A| #b1) (|SS| #b0) (|E| v33) (|TCO| v13) (|I| #b1) (|PAN| v35) (|M| v12) (|D| #b1) (|nRW| #b0) (|EL| #b00) (|IT| v31) (|IL| #b0) (|Z| v3460) (|BTYPE| v19) (|SSBS| v28) (|T| v16) (|J| v32) (|V| v3462) (|DIT| #b0))))
*)
Definition trc_cmp_x1_0 : trc := [
  Smt (DeclareConst 15 (Ty_BitVec 1)) Mk_annot;
  Smt (DeclareConst 20 (Ty_BitVec 1)) Mk_annot;
  Smt (DeclareConst 25 (Ty_BitVec 1)) Mk_annot;
  Smt (DeclareConst 29 (Ty_BitVec 1)) Mk_annot;
  Smt (DeclareConst 3370 (Ty_BitVec 64)) Mk_annot;
  Smt (DefineConst 3371 (Val (Val_Symbolic 3370) Mk_annot)) Mk_annot;
  ReadReg "R1" nil (Val_Symbolic 3371) Mk_annot;
  Smt (DefineConst 3435 (Val (Val_Symbolic 3371) Mk_annot)) Mk_annot;
  Smt (DefineConst 3440 (Manyop (Bvmanyarith Bvadd) [
    Manyop (Bvmanyarith Bvadd) [
      (Unop (ZeroExtend 64) (Val (Val_Symbolic 3435) Mk_annot) Mk_annot);
      (Val (Val_Bits [BV{128} 0x0000000000000000ffffffffffffffff]) Mk_annot)
      ] Mk_annot;
    (Val (Val_Bits [BV{128} 0x00000000000000000000000000000001]) Mk_annot)
  ] Mk_annot)) Mk_annot;
  Smt (DefineConst 3444 (Unop (Extract 63 0) (Val (Val_Symbolic 3440) Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3457 (Manyop Concat [
    Manyop Concat [
      Manyop Concat [
        Manyop (Bvmanyarith Bvor) [
          Manyop (Bvmanyarith Bvand) [
            Val (Val_Bits [BV{1} 0]) Mk_annot;
            Unop Bvnot (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot
          ] Mk_annot;
            (Unop (Extract 0 0) (Binop (Bvarith Bvlshr)
               (Val (Val_Symbolic 3444) Mk_annot)
               (Unop (Extract 63 0) (Val (Val_Bits [BV{128} 0x0000000000000000000000000000003f]) Mk_annot) Mk_annot) Mk_annot) Mk_annot)
        ] Mk_annot;
        Ite (Binop Eq (Val (Val_Symbolic 3444) Mk_annot) (Val (Val_Bits [BV{64} 0x0000000000000000]) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) (Val (Val_Bits [BV{1} 0]) Mk_annot) Mk_annot
       ] Mk_annot;
        Ite (Binop Eq (Unop (ZeroExtend 64) (Val (Val_Symbolic 3444) Mk_annot) Mk_annot) (Val (Val_Symbolic 3440) Mk_annot) Mk_annot) (Val (Val_Bits [BV{1} 0]) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot
     ] Mk_annot;
        Ite (Binop Eq (Unop (SignExtend 64) (Val (Val_Symbolic 3444) Mk_annot) Mk_annot) (
          Manyop (Bvmanyarith Bvadd) [
            Manyop (Bvmanyarith Bvadd) [
Unop (SignExtend 64) (Val (Val_Symbolic 3435) Mk_annot) Mk_annot;
Val (Val_Bits [BV{128} 0xffffffffffffffffffffffffffffffff]) Mk_annot
            ] Mk_annot;
Val (Val_Bits [BV{128} 0x00000000000000000000000000000001]) Mk_annot
          ] Mk_annot
        ) Mk_annot)
        (Val (Val_Bits [BV{1} 0]) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot
   ] Mk_annot)) Mk_annot;
  Smt (DefineConst 3459 (Unop (Extract 3 3) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "N"] (Val_Struct [("N", (Val_Symbolic 29)) ]) Mk_annot;
  WriteReg "PSTATE" [Field "N"] (Val_Struct [("N", (Val_Symbolic 3459)) ]) Mk_annot;
  Smt (DefineConst 3460 (Unop (Extract 2 2) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [ ("Z", (Val_Symbolic 15)) ]) Mk_annot;
  WriteReg "PSTATE" [Field "Z"] (Val_Struct [ ("Z", (Val_Symbolic 3460)) ]) Mk_annot;
  Smt (DefineConst 3461 (Unop (Extract 1 1) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "C"] (Val_Struct [ ("C", (Val_Symbolic 20)) ]) Mk_annot;
  WriteReg "PSTATE" [Field "C"] (Val_Struct [ ("C", (Val_Symbolic 3461)) ]) Mk_annot;
  Smt (DefineConst 3462 (Unop (Extract 0 0) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "V"] (Val_Struct [ ("V", (Val_Symbolic 25)) ]) Mk_annot;
  WriteReg "PSTATE" [Field "V"] (Val_Struct [ ("V", (Val_Symbolic 3462)) ]) Mk_annot
].

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

(* trace of b 0x8: (at 0x000000001030000c)
  (read-reg |_PC| nil #x000000001030000c)
  (branch-address #x0000000010300014)
  (write-reg |_PC| nil #x0000000010300014)
  (write-reg |__PC_changed| nil true))
*)
Definition trc_b_0x8 : trc := [
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x000000001030000c]) Mk_annot;
  BranchAddress (Val_Bits [BV{64} 0x0000000010300014]) Mk_annot;
  WriteReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300014]) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
].

(* trace of bl 0x100: (at address 0x0000000010300010)
(trace
  (read-reg |_PC| nil #x0000000010300010)
  (write-reg |R30| nil #x0000000010300014)
  (read-reg |_PC| nil #x0000000010300010)
  (branch-address #x0000000010300110)
  (write-reg |_PC| nil #x0000000010300110)
  (write-reg |__PC_changed| nil true))
*)
Definition trc_bl_0x100' : trc := [
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300010]) Mk_annot;
  WriteReg "R30" nil (Val_Bits [BV{64} 0x0000000010300014]) Mk_annot;
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300010]) Mk_annot;
  BranchAddress (Val_Bits [BV{64} 0x0000000010300110]) Mk_annot;
  WriteReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300110]) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
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
    <[ "PSTATE" := (Val_Struct
          [("GE", Val_Poison); ("F", Val_Bits [BV{1} 1]);
          ("UAO", Val_Poison); ("C", Val_Bits [BV{1} 0]);
          ("SP", Val_Poison); ("N", Val_Bits [BV{1} 0]);
          ("Q", Val_Poison); ("A", Val_Bits [BV{1} 1]); ("SS", Val_Bits [BV{1} 0]);
          ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Bits [BV{1} 1]);
          ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits [BV{1} 1]);
          ("nRW", Val_Bits [BV{1} 0]); ("EL", Val_Bits [BV{1} 0]);
          ("IT", Val_Poison); ("IL", Val_Bits [BV{1} 0]);
          ("Z", Val_Bits [BV{1} 0]); ("BTYPE", Val_Poison);
          ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
          ("V", Val_Bits [BV{1} 0]); ("DIT", Val_Bits [BV{1} 0])]) ]> $
    <[ "_PC" := Val_Bits start_address ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
                                             ∅;
  seq_nb_state  := false;
|}.
Definition test_state2_global  := {|
  seq_instrs :=
    <[[BV{64} 0x0000000010300000] := [trc_cmp_x1_0]]> $
    <[[BV{64} 0x0000000010300004] := trc_bne_0xc ]> $
    <[[BV{64} 0x0000000010300008] := [trc_mov_x0_1]]> $
    <[[BV{64} 0x000000001030000c] := [trc_b_0x8]]> $
    <[[BV{64} 0x0000000010300010] := [trc_bl_0x100']]> $
    <[[BV{64} 0x0000000010300014] := [trc_mov_OUT_x0]]> $

    <[[BV{64} 0x0000000010300110] := [trc_mov_w0_0]]> $
    <[[BV{64} 0x0000000010300114] := [trc_ret]]> $
    ∅;
  seq_mem := ∅
|}.

Definition test_state2_spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300018] ].

Lemma test_state2_iris `{!islaG Σ} `{!threadG} n1 Hin :
  instr 0x0000000010300000 (Some [trc_cmp_x1_0]) -∗
  instr 0x0000000010300004 (Some trc_bne_0xc ) -∗
  instr 0x0000000010300008 (Some [trc_mov_x0_1]) -∗
  instr 0x000000001030000c (Some [trc_b_0x8]) -∗
  instr 0x0000000010300010 (Some [trc_bl_0x100']) -∗
  instr 0x0000000010300014 (Some [trc_mov_OUT_x0]) -∗
  instr 0x0000000010300018 None -∗
  instr 0x0000000010300110 (Some [trc_mov_w0_0]) -∗
  instr 0x0000000010300114 (Some [trc_ret]) -∗

  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R30" ↦ᵣ Val_Poison -∗
  "R1" ↦ᵣ Val_Bits (BV 64 n1 Hin) -∗
  "R0" ↦ᵣ Val_Poison -∗
  "OUT" ↦ᵣ Val_Poison -∗
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
