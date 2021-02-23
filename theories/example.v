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
  ReadReg (Mk_register_name "R2") Nil (Val_Symbolic (Mk_isla_var 3359)) ();
  Smt (DefineConst (Mk_isla_var 3425) (Var (Mk_isla_var 3359) ())) ();
  ReadReg (Mk_register_name "R3") Nil (Val_Symbolic (Mk_isla_var 3361)) ();
  Smt (DefineConst (Mk_isla_var 3426) (Var (Mk_isla_var 3361) ())) ();
  Smt (DefineConst (Mk_isla_var 3431) (Unop (ZeroExtend 64) (Var (Mk_isla_var 3425) ()) ())) ();
  Smt (DefineConst (Mk_isla_var 3432) (Unop (ZeroExtend 64) (Var (Mk_isla_var 3426) ()) ())) ();
  Smt (DefineConst (Mk_isla_var 3433) (Manyop (Bvmanyarith Bvadd) [Var (Mk_isla_var 3431) (); Var (Mk_isla_var 3432) ()] ())) ();
  Smt (DefineConst (Mk_isla_var 3437) (Unop (Extract 63 0) (Var (Mk_isla_var 3433) ()) ())) ();
  Smt (DefineConst (Mk_isla_var 3452) (Var (Mk_isla_var 3467) ())) ();
  WriteReg (Mk_register_name "R1") Nil (Val_Symbolic (Mk_isla_var 3453)) ()
].
