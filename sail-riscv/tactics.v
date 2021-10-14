Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.

Ltac hnf_sim :=
  match goal with
  | |- sim _ ?e1 _ _ =>
      let e' := eval hnf in e1 in
      change (e1) with e'
  end.

Ltac reduce_closed_sim :=
  repeat match goal with
   | |- context [@subrange_vec_dec ?n ?a ?b ?c ?F1 ?F2] => progress reduce_closed (@subrange_vec_dec n a b c F1 F2)
   | |- context [@access_vec_dec ?n ?w ?m] => progress reduce_closed (@access_vec_dec n w m)
   | |- context [vec_of_bits ?l] => progress reduce_closed (vec_of_bits l)
   | |- context [Word.weqb ?b1 ?b2] => progress reduce_closed (Word.weqb b1 b2)
   | |- context [@eq_vec ?n ?b1 ?b2] => progress reduce_closed (@eq_vec n b1 b2)
   (* | |- context [cast_unit_vec ?b] => progress reduce_closed (cast_unit_vec b) *)
   | |- context [@neq_vec ?n ?b1 ?b2] => progress reduce_closed (@neq_vec n b1 b2)
   | |- context [Z.ltb ?n1 ?n2] => progress reduce_closed (Z.ltb n1 n2)
   | |- context [Z.leb ?n1 ?n2] => progress reduce_closed (Z.leb n1 n2)
   | |- context [Z.geb ?n1 ?n2] => progress reduce_closed (Z.geb n1 n2)
   | |- context [Z.eqb ?n1 ?n2] => progress reduce_closed (Z.eqb n1 n2)
   | |- context [neq_int ?n1 ?n2] => progress reduce_closed (neq_int n1 n2)
   | |- context [size_bits_backwards_matches ?n] => progress reduce_closed (size_bits_backwards_matches n)
   | |- context [size_bits_backwards ?n] => progress reduce_closed (size_bits_backwards n)
   | |- context [bool_bits_backwards_matches ?n] => progress reduce_closed (bool_bits_backwards_matches n)
   | |- context [bool_bits_backwards ?n] => progress reduce_closed (bool_bits_backwards n)
   | |- context [amo_width_valid ?n] => progress reduce_closed (amo_width_valid n)
   | |- context [encdec_amoop_backwards_matches ?n] => progress reduce_closed (encdec_amoop_backwards_matches n)
   | |- context [encdec_amoop_backwards ?n] => progress reduce_closed (encdec_amoop_backwards n)
   | |- context [encdec_mul_op_backwards_matches ?n] => progress reduce_closed (encdec_mul_op_backwards_matches n)
   | |- context [encdec_mul_op_backwards ?n] => progress reduce_closed (encdec_mul_op_backwards n)
   | |- context [bool_not_bits_backwards_matches ?n] => progress reduce_closed (bool_not_bits_backwards_matches n)
   | |- context [bool_not_bits_backwards ?n] => progress reduce_closed (bool_not_bits_backwards n)
   | |- context [encdec_csrop_backwards_matches ?n] => progress reduce_closed (encdec_csrop_backwards_matches n)
   | |- context [encdec_csrop_backwards ?n] => progress reduce_closed (encdec_csrop_backwards n)
   | |- context [encdec_rounding_mode_backwards_matches ?n] => progress reduce_closed (encdec_rounding_mode_backwards_matches n)
   | |- context [encdec_rounding_mode_backwards ?n] => progress reduce_closed (encdec_rounding_mode_backwards n)
(* Decode cannot be reduced for floating point operations. There one has to do something like the following:
  apply: sim_is_RV32F_or_RV64F => b.
  red_sim.
  have -> : (if b then Done false else Done false) = Done false by destruct b.
  red_sim.
*)
   | |- context [riscv.decode ?i] => progress reduce_closed (riscv.decode i)
   | |- context [decodeCompressed ?i] => progress reduce_closed (decodeCompressed i)
   | |- context [get_config_print_reg ()] => progress reduce_closed (get_config_print_reg ())
   end.

Ltac cbn_sim :=
  cbn [returnm bind bind0 sim_regs
       x9_ref x10_ref x11_ref misa_ref PC_ref nextPC_ref
       regval_of of_regval read_from write_to regval_from_reg
       Misa_of_regval regval_of_Misa
       ext_control_check_pc
       bitU_of_bool bool_of_bitU bit_to_bool
       negb sumbool_of_bool set
       projT1 build_ex __id andb orb
       _rec_execute compressed_measure Zwf_guarded
       subst_val_event subst_val_valu subst_val_smt subst_val_exp subst_val_base_val fmap list_fmap eq_var_name Z.eqb Pos.eqb map
    ].

(* Ltac subst_sim := *)
(*   repeat lazymatch goal with *)
(*          | H : ?F (sim_regs ?Σ) = _ |- context [?F (sim_regs ?Σ)] => rewrite H *)
(*          end. *)

Ltac red_monad_sim :=
  repeat lazymatch goal with
         | |- sim _ (_ >>= _) _ _  => apply sim_bind
         | |- sim _ (_ >> _) _ _  => apply sim_bind
         | |- sim _ (and_boolM _ _) _ _  => apply sim_bind
         | |- sim _ (and_boolMP _ _) _ _  => apply sim_bind
         | |- sim _ (projT1_m _) _ _  => apply sim_bind
         | |- sim _ (build_trivial_ex _) _ _  => apply sim_bind
         | |- sim _ (try_catch _ _) _ _  => apply sim_try_catch
         | |- sim _ (Done _) (BindMCtx _ _) _  => apply sim_pop_bind_Done
         | |- sim _ (Done _) (TryMCtx _ _) _  => apply sim_pop_try_Done
         | |- sim _ (assert_exp' _ _) _ _  => apply sim_assert_exp';
              [try done; shelve| let H := fresh in move => H; try clear H]
         | |- sim _ _ _ (Smt (DeclareConst _ (Ty_BitVec _)) _::_)  => apply: sim_DeclareConstBitVec
         | |- sim _ _ _ (Smt (DefineConst _ _) _::_)  => apply: sim_DefineConst; [simpl; done|]
         | |- sim _ _ _ (Smt (Assert _) _::_)  => apply: sim_Assert; [simpl; shelve|]
         | |- sim _ _ _ (Branch _ _ _::_)  => apply: sim_Branch
         | |- sim _ _ _ (BranchAddress _ _::_)  => apply: sim_BranchAddress
         | |- sim _ _ _ (Assume _ _::_)  => let H := fresh "Hassume" in apply: sim_Assume => H; simpl in H
         | |- sim _ (read_reg _) _ (ReadReg _ _ _ _::_)  => apply: sim_read_reg; [done | done | try done; shelve|]
         | |- sim _ (write_reg nextPC_ref _) _ _  => apply: sim_write_reg_private; [done..|]
         | |- sim _ (read_reg nextPC_ref) _ _  => apply: sim_read_reg_l; [done..|]
         | |- sim _ (write_reg _ _) _ (WriteReg _ _ _ _::_)  => apply: sim_write_reg; [done | shelve |]
         | |- sim _ (Done _) NilMCtx []  => apply: sim_done
         end.

Ltac unfold_sim :=
  unfold wX_bits, rX_bits, rX, wX, set_next_pc, regval_from_reg, regval_into_reg, returnm, set.

Ltac red_sim :=
    repeat first [
        progress unfold_sim |
        progress cbn_sim |
        (* progress subst_sim | *)
        progress reduce_closed_sim |
        progress red_monad_sim
      ].

Lemma sim_haveFExt Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (haveFExt ()) K e2.
Proof.
  move => Hsim.
  unfold haveFExt. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  case_match => //. red_sim.
  apply: sim_read_reg_l; [done|].
  by red_sim.
Qed.

Lemma sim_is_RV32F_or_RV64F Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV32F_or_RV64F ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV32F_or_RV64F. red_sim.
  apply: sim_haveFExt => -[]; by red_sim.
Qed.

Lemma sim_is_RV64F Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV64F ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV64F. red_sim.
  apply: sim_haveFExt => -[]; by red_sim.
Qed.

Lemma sim_haveDExt Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (haveDExt ()) K e2.
Proof.
  move => Hsim.
  unfold haveDExt. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  case_match => //. red_sim.
  apply: sim_read_reg_l; [done|].
  by red_sim.
Qed.

Lemma sim_is_RV32D_or_RV64D Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV32D_or_RV64D ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV32D_or_RV64D. red_sim.
  apply: sim_haveDExt => -[]; by red_sim.
Qed.

Lemma sim_is_RV64D Σ K e2:
  (∀ b, sim Σ (Done b) K e2) →
  sim Σ (is_RV64D ()) K e2.
Proof.
  move => Hsim.
  unfold is_RV64D. red_sim.
  apply: sim_haveDExt => -[]; by red_sim.
Qed.
