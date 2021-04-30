Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.

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

(* Lemma add_x1_x2_x3_trace n2 n3 : *)
(*   trc_add_x1_x2_x3 ~{ trace_module, [ *)
(*                     Vis (LReadReg "R2" [] (Val_Bits [BV{64} n2])); *)
(*                     Vis (LReadReg "R3" [] (Val_Bits [BV{64} n3])); *)
(*                     Vis (LWriteReg "R1" [] (Val_Bits (bv_extract 63 0 (bv_add (bv_zero_extend 64 [BV{64} n2]) (bv_zero_extend 64 [BV{64} n3]))))) *)
(*                 ] }~> []. *)
(* Proof. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   do_trace_step. *)
(*   by apply: TraceEnd. *)
(* Qed. *)

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

(* Ltac do_seq_step := *)
(*   apply: (TraceStep' _ _ seq_module (_, _)); [ econstructor; [done|solve_trace_step| try left; done] | done |]; simpl. *)

(* Ltac do_seq_step_jmp := *)
(*   apply: (TraceStep' _ _ seq_module (_, _)); [ econstructor; [done|solve_trace_step| ]; *)
(*                        eexists _, _; repeat (split; first done); vm_compute; split => //; left | done |]; simpl. *)

(* Lemma test_state_trace : *)
(*   (test_state_global, test_state_local) ~{ seq_module, [Vis (SWriteReg "OUT" [] (Val_Bits [BV{64} 0x0])) ] }~> -. *)
(* Proof. *)
(*   eexists _. *)
(*   do_seq_step_jmp. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step_jmp. *)
(*   do_seq_step. *)
(*   do_seq_step_jmp. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step_jmp. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   apply: TraceEnd. *)
(* Qed. *)

Definition test_state_spec : list seq_label := [ SInstrTrap ([BV{64} 0x0000000010300008]) ].

(* Global Instance simpl_normalize_valu_end v1 v2: *)
  (* SimplAndUnsafe true (normalize_valu v1 v2) (λ T, v1 = v2 ∧ T) | 1000. *)
(* Proof. move => ?. done. Qed. *)

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
  simpl.
  repeat liAStep; liShow.
  (*
  repeat liAStep; liShow.
  Unshelve.
  all: done.
Qed.
   *)
  Admitted.

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
  ReadReg "PSTATE" [Field "N"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  WriteReg "PSTATE" [Field "N"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 3459)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  Smt (DefineConst 3460 (Unop (Extract 2 2) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  WriteReg "PSTATE" [Field "Z"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 3459)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 3460));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  Smt (DefineConst 3461 (Unop (Extract 1 1) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "C"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  WriteReg "PSTATE" [Field "C"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 3461));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 3459)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  Smt (DefineConst 3462 (Unop (Extract 0 0) (Val (Val_Symbolic 3457) Mk_annot) Mk_annot)) Mk_annot;
  ReadReg "PSTATE" [Field "V"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  WriteReg "PSTATE" [Field "V"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 3459)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 15));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 3462)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot
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
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 35));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
  Smt (DefineConst 3435 (Unop Not (Binop Eq (Val (Val_Symbolic 35) Mk_annot) (Val (Val_Bits [BV{1} 1]) Mk_annot) Mk_annot) Mk_annot)) Mk_annot;
  Smt (Assert (Val (Val_Symbolic (3435)) Mk_annot)) Mk_annot;
  ReadReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300004]) Mk_annot;
  WriteReg "_PC" nil (Val_Bits [BV{64} 0x0000000010300010]) Mk_annot;
  WriteReg "__PC_changed" nil (Val_Bool true) Mk_annot
]; [
  Smt (DeclareConst 35 (Ty_BitVec 1)) Mk_annot;
  ReadReg "PSTATE" [Field "Z"] (Val_Struct [
    ("GE", (Val_Symbolic 27)); ("F", (Val_Bits [BV{1} 1])); ("UAO", (Val_Symbolic 23)); ("C", (Val_Symbolic 20));
    ("SP", (Val_Bits [BV{1} 1])); ("N", (Val_Symbolic 29)); ("Q", (Val_Symbolic 21)); ("A", (Val_Bits [BV{1} 1]));
    ("SS", (Val_Bits [BV{1} 0])); ("E", (Val_Symbolic 33)); ("TCO", (Val_Symbolic 13)); ("I", (Val_Bits [BV{1} 1]));
    ("PAN", (Val_Symbolic 35)); ("M", (Val_Symbolic 12)); ("D", (Val_Bits [BV{1} 1])); ("nRW", (Val_Bits [BV{1} 0]));
    ("EL", (Val_Bits [BV{1} 0])); ("IT", (Val_Symbolic 31)); ("IL", (Val_Bits [BV{1} 0])); ("Z", (Val_Symbolic 35));
    ("BTYPE", (Val_Symbolic 19)); ("SSBS", (Val_Symbolic 28)); ("T", (Val_Symbolic 16));
    ("J", (Val_Symbolic 32)); ("V", (Val_Symbolic 25)); ("DIT", (Val_Bits [BV{1} 0])) ]) Mk_annot;
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

(*
0x0000000010300000: cmp x1, 0
0x0000000010300004: bne 0xc  --\
0x0000000010300008: mov x0, 1  |
0x000000001030000c: b   0x8    |
0x0000000010300010: bl  0x100<-/
0x0000000010300014: mov OUT, x0


0x0000000010300110: mov x0, 0
0x0000000010300114: ret
*)

Definition bv_1 := [BV{1} 1].
Definition bv_0 := [BV{1} 0].

Definition test_state2_local (n1 : Z) Hin := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "R1" := Val_Bits (BV 64 n1 Hin) ]> $
    <[ "PSTATE" := (Val_Struct
          [("GE", Val_Poison); ("F", Val_Bits bv_1);
          ("UAO", Val_Poison); ("C", Val_Bits bv_0);
          ("SP", Val_Poison); ("N", Val_Bits bv_0);
          ("Q", Val_Poison); ("A", Val_Bits bv_1); ("SS", Val_Bits bv_0);
          ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Bits bv_1);
          ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits bv_1);
          ("nRW", Val_Bits bv_0); ("EL", Val_Bits bv_0);
          ("IT", Val_Poison); ("IL", Val_Bits bv_0);
          ("Z", Val_Bits bv_0); ("BTYPE", Val_Poison);
          ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
          ("V", Val_Bits bv_0); ("DIT", Val_Bits bv_0)]) ]> $
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
    <[[BV{64} 0x0000000010300010] := [trc_bl_0x100]]> $
    <[[BV{64} 0x0000000010300014] := [trc_mov_OUT_x0]]> $

    <[[BV{64} 0x0000000010300110] := [trc_mov_w0_0]]> $
    <[[BV{64} 0x0000000010300114] := [trc_ret]]> $
    ∅;
  seq_mem := ∅
|}.

Definition test_state2_spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300018] ].

Lemma ite_bits b n1 n2 :
  ite b (Val_Bits n1) (Val_Bits n2) = Val_Bits (ite b n1 n2).
Proof. by destruct b. Qed.
Hint Rewrite ite_bits : lithium_rewrite.

Lemma test_state2_iris `{!islaG Σ} `{!threadG} n1 Hin :
  instr 0x0000000010300000 (Some [trc_cmp_x1_0]) -∗
  instr 0x0000000010300004 (Some trc_bne_0xc ) -∗
  instr 0x0000000010300008 (Some [trc_mov_x0_1]) -∗
  instr 0x000000001030000c (Some [trc_b_0x8]) -∗
  instr 0x0000000010300010 (Some [trc_bl_0x100]) -∗
  instr 0x0000000010300014 (Some [trc_mov_OUT_x0]) -∗
  instr 0x0000000010300110 (Some [trc_mov_w0_0]) -∗
  instr 0x0000000010300114 (Some [trc_ret]) -∗

  "_PC" ↦ᵣ Val_Bits start_address -∗
  "__PC_changed" ↦ᵣ Val_Bool false -∗
  "R30" ↦ᵣ Val_Poison -∗
  "R1" ↦ᵣ Val_Bits (BV 64 n1 Hin) -∗
  "R0" ↦ᵣ Val_Poison -∗
  "OUT" ↦ᵣ Val_Poison -∗
  "PSTATE" ↦ᵣ (Val_Struct
          [("GE", Val_Poison); ("F", Val_Bits bv_1);
          ("UAO", Val_Poison); ("C", Val_Bits bv_0);
          ("SP", Val_Poison); ("N", Val_Bits bv_0);
          ("Q", Val_Poison); ("A", Val_Bits bv_1); ("SS", Val_Bits bv_0);
          ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Bits bv_1);
          ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits bv_1);
          ("nRW", Val_Bits bv_0); ("EL", Val_Bits bv_0);
          ("IT", Val_Poison); ("IL", Val_Bits bv_0);
          ("Z", Val_Bits bv_0); ("BTYPE", Val_Poison);
          ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
          ("V", Val_Bits bv_0); ("DIT", Val_Bits bv_0)]) -∗
  spec_trace test_state_spec -∗
  WPasm [].
Proof.
  iStartProof.
  Ltac liASimpl ::= unfold foldr.
  (* cbn [subst_event list_fmap fmap subst_smt subst_valu subst_exp Z.eq_dec Z_rec Z_rect sumbool_rec sumbool_rect Pos.eq_dec positive_rec positive_rect foldr]. *)
  Ltac liSideCond ::=
    idtac;
  lazymatch goal with
  | |- ?P ∧ ?Q => first [
    let P' := eval simpl in P in
    progress change_no_check (P' ∧ Q)
    |
    lazymatch P with
    | shelve_hint _ => split; [ unfold shelve_hint; shelve |]
    | _ => first [ progress normalize_goal_and |
    lazymatch P with
    | context [protected _] => first [
        split; [ solve_protected_eq |]; unfold_instantiated_evars
      | notypeclasses refine (apply_simpl_and _ _ _ _ _); [ solve [refine _] |]; simpl;
        lazymatch goal with
        | |- true = true -> _ => move => _
        | _ => fail "could not simplify goal with evar"
        end
      ]
    | _ => split; [ first [ fast_done | shelve ] | ]
    end ] end ]
  | _ => fail "do_side_cond: unknown goal"
  end.
  do 100 liAStep; liShow.
  Set Ltac Profiling.
  Reset Ltac Profile.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   (* TODO: VM compute here is not a good idea as it probably unfolds bv_add. *)

   set H := ((bv_add (bv_add (bv_zero_extend 64 [BV{64} n1]) [BV{128} 18446744073709551615]) [BV{128} 1])).

   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
   liAStep; liShow.
.
  Show Ltac Profile.
  liAStep; liShow.
  liAStep; liShow.

  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
 Ltac Profile.
  unfold foldr.
  repeat liAStep; liShow.
  unfold foldr.
  repeat liAStep; liShow.
  unfold foldr.
  Set Nested Proofs Allowed.
  Import environments.
  Lemma tac_subst_event `{!islaG Σ} `{!threadG} Δ n v es es':
    subst_event n v <$> es = es' →
    envs_entails Δ (WPasm es') →
    envs_entails Δ (WPasm (subst_event n v <$> es)).
  Proof. move => ->. done. Qed.

  lazymatch goal with
  | |- envs_entails ?Δ (WPasm ?es) =>
    lazymatch es with
    | (subst_event _ _ <$> _) =>
      notypeclasses refine (tac_subst_event _ _ _ _ _ _ _); [vm_compute; exact eq_refl|]
    end
  end.


    do 100 liAStep; liShow.
  Show Ltac Profile.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  cbn [foldr].
  | |- context =>
  unfold bool_decide, decide_rel, Z_eq_dec, Z.eq_dec, Z_rec, Z_rect, sumbool_rec, sumbool_rect, Pos.eq_dec, positive_rec, positive_rect.
  cbn [sumbool_rec sumbool_rect Pos.eq_dec positive_rec positive_rect].
  unfold bool_decide, decide_rel, Z_eq_dec, Z.eq_dec, Z_rec, Z_rect, sumbool_rec, sumbool_rect, Pos.eq_dec, positive_rec, positive_rect.
  Set Printing Implicit.
  simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  repeat liAStep; liShow. simpl.
  do 100 liAStep; liShow.
  do 100 liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  Set Ltac Profiling.
  Reset Ltac Profile.
  liAStep.
  Show Ltac Profile.
  simpl.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.
  liAStep; liShow.



  (* do 10 liAStep; liShow. *)


(*
  do 10 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
  do 20 liAStep; liShow.
*)
  (* repeat liAStep; liShow. *)
Abort.


(* Lemma test_state2_trace x1 : *)
(*   (test_state2_global, test_state2_local x1) ~{ seq_module, [Vis (SWriteReg "OUT" [] (Val_Bits [BV{64} 0])) ] }~> -. *)
(* Proof. *)
(*   eexists _. *)
(*   do_seq_step_jmp. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(*   do_seq_step. *)
(* Abort. *)

(*
trace of ldr x0, [x1]: (trace of str x0, [x1] is similar, only with write-mem)
(trace
  (branch-address #x0000000010300000)
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3486 (bvadd v3371 #x0000000000000000))
  (write-reg |__LSISyndrome| nil #b11100000010)
  (define-const v3512 (not (= v3486 (bvand v3486 #xfffffffffffffff8))))
  (branch 0 "SourceLoc { file: 6, line1: 13232, char1: 4, line2: 13235, char2: 5 }")
  (assert v3512)
  (declare-const v3517 Bool)
  (read-reg |_PC| nil #x0000000010300000)
  (branch 1 "SourceLoc { file: 3, line1: 6794, char1: 41, line2: 6794, char2: 77 }")
  (assert v3517)
  (define-const v3630 v3486)
  (assert v3517)
  (... saving processor state ...)
  (write-reg |_PC| nil #x0000000000000400)
  (write-reg |__PC_changed| nil true))
(trace
  (branch-address #x0000000010300000)
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3486 (bvadd v3371 #x0000000000000000))
  (write-reg |__LSISyndrome| nil #b11100000010)
  (define-const v3512 (not (= v3486 (bvand v3486 #xfffffffffffffff8))))
  (branch 0 "SourceLoc { file: 6, line1: 13232, char1: 4, line2: 13235, char2: 5 }")
  (assert v3512)
  (declare-const v3517 Bool)
  (read-reg |_PC| nil #x0000000010300000)
  (branch 1 "SourceLoc { file: 3, line1: 6794, char1: 41, line2: 6794, char2: 77 }")
  (assert (not v3517))
  (define-const v3630 v3486)
  (assert (not v3517))
  (... saving processor state ...)
  (write-reg |_PC| nil #x0000000000000400)
  (write-reg |__PC_changed| nil true))
(trace
  (branch-address #x0000000010300000)
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3486 (bvadd v3371 #x0000000000000000))
  (write-reg |__LSISyndrome| nil #b11100000010)
  (define-const v3491 (= v3486 (bvand v3486 #xfffffffffffffff8)))
  (define-const v3512 (not v3491))
  (branch 0 "SourceLoc { file: 6, line1: 13232, char1: 4, line2: 13235, char2: 5 }")
  (assert (not v3512))
  (assert (not (not v3491)))
  (assert (= v3486 (bvand v3486 #xfffffffffffffff8)))(call |AArch64_aget_MemSingle|)
  (define-const v4369 (= (bvor #b0 ((_ extract 0 0) (bvlshr v3486 #x0000000000000037))) #b1))
  (branch 1 "SourceLoc { file: 3, line1: 6170, char1: 20, line2: 6170, char2: 81 }")
  (assert v4369)
  (assert (not (= ((_ extract 63 52) v3486) #x000)))
  (assert (not (not v3491)))(return |AArch64_TranslateAddress|)
  (... saving processor state ...)
  (write-reg |_PC| nil #x0000000000000400)
  (write-reg |__PC_changed| nil true))
(trace
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3486 (bvadd v3371 #x0000000000000000))
  (write-reg |__LSISyndrome| nil #b11100000010)
  (define-const v3491 (= v3486 (bvand v3486 #xfffffffffffffff8)))
  (define-const v3512 (not v3491))
  (branch 0 "SourceLoc { file: 6, line1: 13232, char1: 4, line2: 13235, char2: 5 }")
  (assert (not v3512))
  (assert (not (not v3491)))
  (assert (= v3486 (bvand v3486 #xfffffffffffffff8)))(call |AArch64_aget_MemSingle|)
  (define-const v4369 (= (bvor #b0 ((_ extract 0 0) (bvlshr v3486 #x0000000000000037))) #b1))
  (branch 1 "SourceLoc { file: 3, line1: 6170, char1: 20, line2: 6170, char2: 81 }")
  (assert (not v4369))
  (define-const v4376 (not (= ((_ extract 63 52) v3486) #x000)))
  (branch 2 "SourceLoc { file: 3, line1: 6443, char1: 4, line2: 6452, char2: 5 }")
  (assert v4376)
  (assert (not (not v3491)))(return |AArch64_TranslateAddress|)
  (... saving processor state ...)
  (write-reg |_PC| nil #x0000000000000400)
  (write-reg |__PC_changed| nil true))
(trace
  (declare-const v3370 (_ BitVec 64))
  (define-const v3371 v3370)
  (read-reg |R1| nil v3371)
  (define-const v3486 (bvadd v3371 #x0000000000000000))
  (write-reg |__LSISyndrome| nil #b11100000010)
  (define-const v3491 (= v3486 (bvand v3486 #xfffffffffffffff8)))
  (define-const v3512 (not v3491))
  (branch 0 "SourceLoc { file: 6, line1: 13232, char1: 4, line2: 13235, char2: 5 }")
  (assert (not v3512))
  (assert (not (not v3491)))
  (assert (= v3486 (bvand v3486 #xfffffffffffffff8)))(call |AArch64_aget_MemSingle|)
  (define-const v4369 (= (bvor #b0 ((_ extract 0 0) (bvlshr v3486 #x0000000000000037))) #b1))
  (branch 1 "SourceLoc { file: 3, line1: 6170, char1: 20, line2: 6170, char2: 81 }")
  (assert (not v4369))
  (define-const v4376 (not (= ((_ extract 63 52) v3486) #x000)))
  (branch 2 "SourceLoc { file: 3, line1: 6443, char1: 4, line2: 6452, char2: 5 }")
  (assert (not v4376))
  (assert (not (not v3491)))
  (read-reg |PSTATE| ((_ field |D|)) (_ struct (|F| #b1) (|V| v26) (|TCO| v18) (|A| #b1) (|Q| v34) (|IL| #b0) (|M| v16) (|GE| v21) (|nRW| #b0) (|BTYPE| v29) (|EL| #b00) (|I| #b1) (|C| v27) (|PAN| v37) (|J| v24) (|SP| #b1) (|UAO| v17) (|T| v14) (|N| v19) (|D| #b1) (|DIT| #b0) (|IT| v13) (|E| v23) (|Z| v30) (|SSBS| v32) (|SS| #b0)))
  (read-reg |OSLSR_EL1| nil v440)
  (assert (= (bvor #b0 ((_ extract 0 0) (bvlshr v440 #x00000001))) #b1))
  (read-reg |EDSCR| nil v1)
  (assert (not (= ((_ extract 5 0) v1) #b000001)))
  (read-reg |EDSCR| nil v1)
  (assert (not (not (= ((_ extract 5 0) v1) #b000010))))
  (read-reg |OSDLR_EL1| nil v438)
  (assert (not (= (bvor (bvand #b0 (bvnot #b1)) ((_ extract 0 0) (bvlshr v438 ((_ extract 31 0) #x00000000000000000000000000000000)))) #b1)))
  (read-reg |DBGEN| nil e2_0)(return |AArch64_TranslateAddress|)
  (declare-const v4792 (_ BitVec 56))
  (read-reg |__defaultRAM| nil v4792)
  (define-const v4807 ((_ zero_extend 8) (concat #x0 ((_ extract 51 0) v3486))))
  (declare-const v4808 (_ BitVec 64))
  (read-mem v4808 e7_0 v4807 8 None)
  (define-const v4829 v4808)
  (write-reg |R0| nil v4829))
*)
