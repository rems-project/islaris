Require Import isla.base.
Require Import isla.opsem.

Ltac solve_trace_step := by econstructor.
Ltac do_trace_step :=
  apply: TraceStep'; [solve_trace_step | done |]; simpl.


(* trace of add x1, x2, x3:
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

Lemma add_x1_x2_x3_trace bv2 bv3 :
  trc_add_x1_x2_x3 ~{ trace_module, [
                    Vis (LReadReg "R2" [] (Val_Bits bv2));
                    Vis (LReadReg "R3" [] (Val_Bits bv3));
                    Vis (LWriteReg "R1" [] (Val_Bits (Z_extract 63 0 (bv2 + bv3))))
                ] }~> [].
Proof.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  do_trace_step.
  by apply: TraceEnd.
Qed.

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
   WriteReg "R0" [] (Val_Bits 0x0000000000000000) Mk_annot
  ].

Definition trc_mov_x0_1 : trc := [
   WriteReg "R0" [] (Val_Bits 0x0000000000000001) Mk_annot
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
  ReadReg "_PC" nil (Val_Bits 0x0000000010300000) Mk_annot;
  WriteReg "R30" nil (Val_Bits 0x0000000010300004) Mk_annot;
  ReadReg "_PC" nil (Val_Bits 0x0000000010300000) Mk_annot;
  BranchAddress (Val_Bits 0x0000000010300100) Mk_annot;
  WriteReg "_PC" nil (Val_Bits 0x0000000010300100) Mk_annot;
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
  Smt (DefineConst 3450 (Manyop (Bvmanyarith Bvor) [Val (Val_Bits 0x0000000000000000) Mk_annot; Val (Val_Symbolic 3369) Mk_annot] Mk_annot)) Mk_annot;
  WriteReg "OUT" nil (Val_Symbolic 3450) Mk_annot
].

Definition test_state := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "_PC" := Val_Bits (0x0000000010300000 - 0x4) ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
     ∅;
  seq_instrs :=
    <[0x0000000010300000 := [trc_bl_0x100]]> $   (* bl 0x100: (at address 0x0000000010300000 *)
    <[0x0000000010300004 := [trc_mov_OUT_x0]]> $ (* mov OUT, x0 *)
    <[0x0000000010300100 := [trc_mov_w0_0]]> $   (* mov w0, 0 *)
    <[0x0000000010300104 := [trc_ret]]> $        (* ret *)
    ∅
|}.

Ltac do_seq_step :=
  apply: TraceStep'; [ econstructor; [solve_trace_step| done] | done |]; simpl.

Ltac do_seq_step_jmp :=
  apply: TraceStep'; [ econstructor; [solve_trace_step| ];
                       eexists _, _; repeat (split; first done); vm_compute; split => //; left | done |]; simpl.

Lemma test_state_trace :
  test_state ~{ seq_module, [Vis (SWriteReg "OUT" [] (Val_Bits 0)) ] }~> -.
Proof.
  eexists _.
  do_seq_step_jmp.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step_jmp.
  do_seq_step.
  do_seq_step_jmp.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step_jmp.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  do_seq_step.
  apply: TraceEnd.
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
  (* TODO: Add support for reading fields to the semantics: everything except the field should be ignored. *)
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
(* TODO *)
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
(* TODO *)
].

(* trace of b 0x8: (at 0x000000001030000c)
  (read-reg |_PC| nil #x000000001030000c)
  (branch-address #x0000000010300014)
  (write-reg |_PC| nil #x0000000010300014)
  (write-reg |__PC_changed| nil true))
*)
Definition trc_b_0x8 : trc := [
  ReadReg "_PC" nil (Val_Bits 0x000000001030000c) Mk_annot;
  BranchAddress (Val_Bits 0x0000000010300014) Mk_annot;
  WriteReg "_PC" nil (Val_Bits 0x0000000010300014) Mk_annot;
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


Definition test_state2 (x1 : Z) := {|
  seq_trace  := [];
  seq_regs   :=
    <[ "R1" := Val_Bits x1 ]> $
    <[ "_PC" := Val_Bits (0x0000000010300000 - 0x4) ]> $
    <[ "__PC_changed" := Val_Bool false ]> $
     ∅;
  seq_instrs :=
    <[0x0000000010300000 := [trc_cmp_x1_0]]> $
    <[0x0000000010300004 := trc_bne_0xc ]> $
    <[0x0000000010300008 := [trc_mov_x0_1]]> $
    <[0x000000001030000c := [trc_b_0x8]]> $
    <[0x0000000010300010 := [trc_bl_0x100]]> $
    <[0x0000000010300014 := [trc_mov_OUT_x0]]> $

    <[0x0000000010300110 := [trc_mov_w0_0]]> $
    <[0x0000000010300114 := [trc_ret]]> $
    ∅
|}.

Lemma test_state2_trace x1 :
  test_state2 x1 ~{ seq_module, [Vis (SWriteReg "OUT" [] (Val_Bits 0)) ] }~> -.
Proof.
  eexists _.
  do_seq_step_jmp.
  (* do_seq_step. *)
Abort.
