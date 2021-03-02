Require Import isla.base.
Require Import isla.opsem.

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
Definition add_x1_x2_x3 : trc :=
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
  add_x1_x2_x3 ~{ trace_module, [
                    Vis (LReadReg "R2" [] (Val_Bits bv2));
                    Vis (LReadReg "R3" [] (Val_Bits bv3));
                    Vis (LWriteReg "R1" [] (Val_Bits (Z_extract 63 0 (bv2 + bv3))))
                ] }~> [].
Proof.
  apply: TraceStepNone. { apply: (DeclareConstS (Val_Bits _)). shelve. } simpl.
  apply: TraceStepNone. { apply: (DeclareConstS (Val_Bits _)). shelve. } simpl.
  apply: TraceStepSome. { econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepSome. { econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepNone. { by econstructor. } simpl.
  apply: TraceStepSome. { econstructor. } simpl.
  by apply: TraceEnd.
Qed.
