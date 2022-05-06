(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.bitvector_auto.
Require Import isla.sail_riscv.sail_opsem.

Arguments read_accessor : simpl nomatch.

Ltac hnf_sim :=
  match goal with
  | |- sim _ ?e1 _ _ =>
      let e' := eval hnf in e1 in
      change (e1) with e'
  end.

Ltac reduce_closed_mword_to_bv :=
  repeat match goal with
  | |- context [@mword_to_bv ?n1 ?n2 ?b] => reduce_closed (@mword_to_bv n1 n2 b)
  end.

Ltac reduce_closed_sim :=
  repeat match goal with
   | |- context [@subrange_vec_dec ?n ?a ?b ?c ?F1 ?F2] => progress reduce_closed (@subrange_vec_dec n a b c F1 F2)
   | |- context [@access_vec_dec ?n ?w ?m] => progress reduce_closed (@access_vec_dec n w m)
   | |- context [vec_of_bits ?l] => progress reduce_closed (vec_of_bits l)
   | |- context [Word.weqb ?b1 ?b2] => progress reduce_closed (Word.weqb b1 b2)
   | |- context [@eq_vec ?n ?b1 ?b2] => progress reduce_closed (@eq_vec n b1 b2)
   | |- context [eq_bit ?b1 ?b2] => progress reduce_closed (eq_bit b1 b2)
   (* | |- context [cast_unit_vec ?b] => progress reduce_closed (cast_unit_vec b) *)
   | |- context [@neq_vec ?n ?b1 ?b2] => progress reduce_closed (@neq_vec n b1 b2)
   | |- context [@generic_eq ?T ?x ?y ?D] => progress reduce_closed (@generic_eq T x y D)
   | |- context [@generic_neq ?T ?x ?y ?D] => progress reduce_closed (@generic_neq T x y D)
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
  cbn [returnM returnm bind bind0 sim_regs
       x1_ref x2_ref x9_ref x10_ref x11_ref x12_ref misa_ref mstatus_ref PC_ref nextPC_ref cur_privilege_ref
       regval_of of_regval read_from write_to regval_from_reg
       Misa_of_regval regval_of_Misa
       read_kind_of_flags
       ext_control_check_pc
       bitU_of_bool bool_of_bitU bit_to_bool
       extend_value MemoryOpResult_drop_meta
       negb sumbool_of_bool set
       projT1 build_ex __id andb orb
       _rec_execute compressed_measure Zwf_guarded
       subst_trace subst_val_event subst_val_valu subst_val_smt subst_val_exp subst_val_base_val fmap list_fmap eq_var_name Z.eqb Pos.eqb map
    ].

Create HintDb simpl_regs_rewrite.
#[export]
Hint Rewrite x1_nextPC x2_nextPC x10_nextPC nextPC_x10 x11_nextPC nextPC_x11
  x12_nextPC nextPC_x12 x13_nextPC nextPC_x13 mstatus_nextPC misa_nextPC
  cur_privilege_nextPC PC_nextPC nextPC_nextPC : simpl_regs_rewrite.
Ltac sim_simpl_regs :=
  autorewrite with simpl_regs_rewrite.

(* Create HintDb mword_to_bv_rewrite. *)
(* #[export] *)
(* Hint Rewrite @mword_to_bv_add_vec using done : mword_to_bv_rewrite. *)

Ltac shelve_types :=
  lazymatch goal with
  | |- ?G =>
      lazymatch type of G with
      | Prop => idtac
      | _ => shelve
      end
  end.
Ltac sim_simpl_goal :=
  shelve_types; simpl; sim_simpl_regs;
  repeat lazymatch goal with
         | |- Some ?a = Some ?b => apply f_equal_help; [done|]
         | |- Val_Bool ?a = Val_Bool ?b => apply f_equal_help; [done|]
         | |- Val_Bits ?a = Val_Bits ?b => apply f_equal_help; [done|]
         | |- bv_to_bvn ?a = bv_to_bvn ?b => apply f_equal_help; [done|]
         | |- Val_Enum ?a = Val_Enum ?b => apply f_equal_help; [done|]
         | |- RegVal_Base ?a = RegVal_Base ?b => apply f_equal_help; [done|]
         | |- RegVal_Struct ?a = RegVal_Struct ?b => apply f_equal_help; [done|]
         | |- Mk_enum_id ?a = Mk_enum_id ?b => apply f_equal_help; [done|]
         | |- (?a1, ?a2) = (?b1, ?b2) => apply f_equal_help; [apply f_equal_help; [done|] |]
         | |- _::_ = _::_ => apply f_equal_help; [apply f_equal_help; [done|] |]
         end;
  try lazymatch goal with | |- negb _ = true => apply negb_true_iff end;
  try lazymatch goal with | |- negb _ = false => apply negb_false_iff end;
  try apply bool_decide_eq_true_2;
  try apply bool_decide_eq_false_2;
  (* autorewrite with mword_to_bv_rewrite; *)
  try done.

(* Ltac subst_sim := *)
(*   repeat lazymatch goal with *)
(*          | H : ?F (sim_regs ?Σ) = _ |- context [?F (sim_regs ?Σ)] => rewrite H *)
(*          end. *)
Ltac sim_simpl_hyp H :=
  try (injection H; clear H; intros H);
  try lazymatch type of H with negb _ = true => apply negb_true_iff in H end;
  try lazymatch type of H with negb _ = false => apply negb_false_iff in H end;
  try apply bool_decide_eq_true_1 in H;
  try apply bool_decide_eq_false_1 in H;
  try (apply Eqdep_dec.inj_pair2_eq_dec in H; [|by move => ??; apply decide; apply _]).

Ltac red_monad_sim :=
  repeat match goal with
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
         | |- sim _ _ _ (Smt (DeclareConst _ Ty_Bool) _:t:_)  => apply: sim_DeclareConstBool
         | |- sim _ _ _ (Smt (DeclareConst _ (Ty_BitVec _)) _:t:?e2) =>
             lazymatch e2 with
             | ReadMem _ _ _ _ _ _ :t: _ => fail
             | _ => apply: sim_DeclareConstBitVec
             end
         | |- sim _ _ _ (Smt (DeclareConst _ (Ty_Enum _)) _:t:_)  => apply: sim_DeclareConstEnum
         | |- sim _ _ _ (Smt (DefineConst _ _) _:t:_)  => apply: sim_DefineConst; [simpl; done|]
         | |- sim _ _ _ (Smt (Assert _) _:t:_)  => apply: sim_Assert; [simpl; shelve|]
         | |- sim _ _ _ (Branch _ _ _:t:_)  => apply: sim_Branch
         | |- sim _ _ _ (BranchAddress _ _:t:_)  => apply: sim_BranchAddress
         | |- sim _ _ _ (Assume _ _:t:_)  =>
             let H := fresh "Hassume" in apply: sim_Assume => H; simpl in H; sim_simpl_hyp H
         | |- sim _ _ _ (AssumeReg _ _ _ _:t:_)  =>
             let H := fresh "Hassume" in apply: sim_AssumeReg => H; simpl in H; sim_simpl_hyp H
         | |- sim _ _ _ (ReadReg _ _ _ _:t:_)  => apply: sim_ReadReg_config; [reflexivity | try done; shelve|]
         | |- sim _ (read_reg _) _ (ReadReg _ _ _ _:t:_)  => apply: sim_read_reg; [done | done | try done; shelve|]
         | |- sim _ (write_reg nextPC_ref _) _ _  => apply: sim_write_reg_private; [done..|]
         | |- sim _ (read_reg nextPC_ref) _ _  => apply: sim_read_reg_l; [done..|]
         | |- sim _ (get_next_pc ()) _ _  => apply: sim_read_reg_l; [done..|]
         | |- sim _ (write_reg _ _) _ (WriteReg _ _ _ _:t:_)  => apply: sim_write_reg; [done | done | shelve |]
         | |- sim _ (Write_ea _ _ _ _) _ _  => apply: sim_Write_ea
         | |- sim _ (Prompt_monad.write_mem _ _ _ _ _) _ (WriteMem _ _ _ _ _ _ _ :t:_)  => apply sim_write_mem; [done|done|done|done|shelve|shelve|]
         | |- sim _ (Prompt_monad.read_mem _ _ _ _) _ (Smt (DeclareConst _ (Ty_BitVec _)) _:t:ReadMem _ _ _ _ _ _ :t:_) =>
             apply sim_read_mem; [done|done|done|shelve|] => ?? ->
         | |- sim _ (Done _) NilMCtx tnil  => apply: sim_done
         end.


Ltac unfold_sim :=
  unfold wX_bits, rX_bits, rX, wX, set_next_pc, regval_from_reg, regval_into_reg, returnM, returnm, set, ext_data_get_addr,
    mem_write_ea, write_ram_ea, write_mem_ea, phys_mem_write, write_ram, phys_mem_read, read_ram, process_load,
    mem_write_value_priv_meta, pmp_mem_write, checked_mem_write, mem_read_priv, mem_read_priv_meta, pmp_mem_read,
    checked_mem_read.


Ltac red_sim :=
    repeat first [
        progress unfold_sim |
        progress cbn_sim |
        (* progress subst_sim | *)
        progress reduce_closed_sim |
        progress red_monad_sim
      ].

Lemma check_misaligned_false b w:
  bv_unsigned (bv_extract 0 (match w with | BYTE => 0 | HALF => 1 | WORD => 2 | DOUBLE => 3 end) (mword_to_bv (n2:=64) b)) = 0 →
  check_misaligned b w = false.
Proof.
  move => He. rewrite /check_misaligned.
  destruct (plat_enable_misaligned_access ()) => //.
  rewrite !access_vec_dec_to_bv //.
  bv_simplify He. case_match => //; rewrite !bitU_of_bool_B0 //.
  all: by lazymatch goal with | |- Z.testbit _ ?n = _ => bitblast He with n end.
Qed.

Lemma within_mmio_writable_false b w H z:
  z = bv_unsigned (mword_to_bv (n2:=64) b) →
  (z < bv_unsigned (mword_to_bv (n2:=64) (plat_clint_base ())) ∨
    bv_unsigned (mword_to_bv (n2:=64) (plat_clint_base ())) +
      bv_unsigned (mword_to_bv (n2:=64) (plat_clint_size ())) < z + w)
  ∧
  (
  bv_unsigned (mword_to_bv (n2:=64) (to_bits 64 (elf_tohost ()))) ≠ z ∧
    (bv_wrap 64 (bv_unsigned (mword_to_bv (n2:=64) (to_bits 64 (elf_tohost ()))) + 4) ≠ z ∨ w ≠ 4) ∨ 8 < w)
  →
  @within_mmio_writable b w H = false.
Proof.
  move => -> [Hclint Helf].
  rewrite /within_mmio_writable/within_clint/within_htif_writable. apply orb_false_intro.
  - apply andb_false_iff. rewrite !Z.leb_gt. by rewrite /uint/= !uint_plain_to_bv_unsigned.
  - rewrite andb_false_iff orb_false_iff andb_false_iff /= Z.eqb_neq !Z.leb_gt.
    by rewrite !(eq_vec_to_bv 64) // !bool_decide_eq_false !bv_neq mword_to_bv_add_vec.
Qed.

Lemma within_phys_mem_true b w H z:
  z = bv_unsigned (mword_to_bv (n2:=64) b) →
  bv_unsigned (mword_to_bv (n2:=64) (plat_ram_base ())) ≤ z
  ∧ z + w
    ≤ bv_unsigned (mword_to_bv (n2:=64) (plat_ram_base ())) +
      bv_unsigned (mword_to_bv (n2:=64) (plat_ram_size ())) →
  @within_phys_mem b w H = true.
Proof.
  move => -> ?. rewrite /within_phys_mem.
  by rewrite andb_true_intro // !Z.leb_le /uint/= !uint_plain_to_bv_unsigned.
Qed.


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

Lemma bv_extract_17_1_and (b : bv 64):
  bv_and b (BV 64 0x20000) = (BV 64 0) →
  bv_extract 17 1 b = (BV 1 0).
Proof. move => Hb. bv_simplify. bitblast as n. bv_simplify Hb. by bitblast Hb with (n + 17). Qed.

Lemma sim_effectivePrivilege Σ K t m priv e2:
  bv_and (mword_to_bv (n2:=64) (Mstatus_bits m)) (BV 64 0x20000) = (BV 64 0) →
  sim Σ (Done priv) K e2 →
  sim Σ (effectivePrivilege t m priv) K e2.
Proof.
  move => Hm Hsim.
  unfold effectivePrivilege.
  destruct t as [[]|[]|[[] []]|[]]; red_sim => //; rewrite if_false //.
  all: unfold _get_Mstatus_MPRV; rewrite (eq_vec_to_bv 1); [|done].
  all: by rewrite (mword_to_bv_subrange_vec_dec 17 17 64) // bv_extract_17_1_and.
Qed.
