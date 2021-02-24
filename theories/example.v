Require Import isla.base.
Require Import isla.isla_lang.

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
  Trace [
  ReadReg "R2" Nil (Val_Symbolic 3359) Mk_annot;
  Smt (DefineConst 3425 (Var 3359 Mk_annot)) Mk_annot;
  ReadReg "R3" Nil (Val_Symbolic 3361) Mk_annot;
  Smt (DefineConst 3426 (Var 3361 Mk_annot)) Mk_annot;
  Smt (DefineConst 3431 (Unop (ZeroExtend 64) (Var 3425 Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3432 (Unop (ZeroExtend 64) (Var 3426 Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3433 (Manyop (Bvmanyarith Bvadd) [Var 3431 Mk_annot; Var 3432 Mk_annot] Mk_annot)) Mk_annot;
  Smt (DefineConst 3437 (Unop (Extract 63 0) (Var 3433 Mk_annot) Mk_annot)) Mk_annot;
  Smt (DefineConst 3452 (Var 3467 Mk_annot)) Mk_annot;
  WriteReg "R1" Nil (Val_Symbolic 3453) Mk_annot
].
