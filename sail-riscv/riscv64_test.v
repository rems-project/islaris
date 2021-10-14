Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
Require Import isla.sail_riscv.tactics.
Require Import isla.automation.
From isla.instructions.riscv64_test Require Import instrs.
Require Import isla.examples.riscv64_test.

Lemma sim_instr_a0:
  sim_instr (Uncompressed [BV{32} 0x00000513]) a0.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve.
  all: try done.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed [BV{32} 0x00150513]) a4.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve.
  all: try done.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
  - simpl. destruct regs => /=. rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a8:
  sim_instr (Uncompressed [BV{32} 0x00b50463]) a8.
Proof.
  move => regs.
  destruct (eq_vec (x10 regs) (x11 regs)) eqn: Hb1.
  all: eexists _; split. 1: by right; left. 2: by left.
  all: unfold step_cpu; red_sim; unfold execute; red_sim.
  all: unfold execute_BTYPE; red_sim.
  all: apply: sim_read_reg_l; [done|]; red_sim.
  all: rewrite x10_nextPC x11_nextPC Hb1; red_sim.
  rewrite bit_to_bool_false; [|shelve]. red_sim.
  Unshelve.
  all: rewrite /= ?x10_nextPC ?x11_nextPC ?PC_nextPC ?nextPC_nextPC; simpl; try done.
  - rewrite (eq_vec_to_bv 64) // in Hb1. by rewrite Hb1.
  - move: Hassume. normalize_and_simpl_goal => //= Hb.
    have Hbit : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (PC regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    bitify_hyp Hb. move: (Hb 0 ltac:(done)) => {}Hb.
    bits_simplify_hyp Hb.
    rewrite Z.add_bit1 Hbit andb_false_r in Hb. done.
  - move: Hassume. normalize_and_simpl_goal => //=.
    have Hbit : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (PC regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    bits_simplify. have ? : n = 0 by lia. subst.
    by rewrite Z.add_bit1 Hbit andb_false_r.
  - rewrite (eq_vec_to_bv 64) // in Hb1. by rewrite Hb1.
  - rewrite mword_to_bv_add_vec //.
  - move: Hassume. normalize_and_simpl_goal => //=.
    apply bitU_of_bool_B0.
    rewrite (getBit_get_word_testbit 64) // mword_to_bv_add_vec //=.
    match goal with
    | |- context [@mword_to_bv ?n1 ?n2 ?b] => reduce_closed (@mword_to_bv n1 n2 b)
    end.
    rewrite bv_add_unsigned bv_wrap_spec_low // Z.add_bit1 /=.
    have -> : (Z.testbit (bv_unsigned (mword_to_bv (n2:=64) (PC regs))) 1) = false. {
      rename select (bv_extract 1 1 _ = _) into He.
      bitify_hyp He. move: (He 0 ltac:(done)) => {}He.
      by bits_simplify_hyp He.
    }
    by rewrite andb_false_r.
  - rewrite mword_to_bv_add_vec //.
Qed.

Definition riscv_test_sail_instrs : gmap addr encoded_instruction :=
  <[ [BV{64} 0x0000000010300000] := Uncompressed [BV{32} 0x00000513]]> $
  <[ [BV{64} 0x0000000010300004] := Uncompressed [BV{32} 0x00150513]]> $
  <[ [BV{64} 0x0000000010300008] := Uncompressed [BV{32} 0x00b50463]]> $
  ∅.

Definition riscv_test_initial_sail_state (regs : regstate) : sail_state :=
  SAIL (Done tt) regs ∅ riscv_test_sail_instrs false.

Lemma riscv_test_safe regs (x11v : bv 64):
  PC regs = bv_to_mword [BV{64} 0x0000000010300000] →
  x11 regs = bv_to_mword x11v →
  misa regs = {| Misa_Misa_chunk_0 := bv_to_mword misa_bits |} →
  safe sail_module (riscv_test_initial_sail_state regs) ∧
    (∀ κs σ', steps sail_module (riscv_test_initial_sail_state regs) κs σ' → riscv_test_spec x11v κs).
Proof.
  move => HPC Hx11 Hmisa.
  apply: iris_transfer_refines.
  { apply iris_module_wf_isla_lang. }
  { apply riscv_test_adequate. }
  apply: sim_implies_refines.
  - rewrite !dom_insert_L !dom_empty_L. set_solver.
  - move => ??.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq => //.
    all: unfold get_regval; simpl; eexists _; split; [done|].
    + by rewrite HPC.
    + done.
    + rewrite Hx11 /= mword_to_bv_to_mword //.
    + rewrite Hmisa /= mword_to_bv_to_mword //.
  - done.
  - unfold riscv_test_sail_instrs. move => ??? Hsail.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq.
    + apply sim_instr_a0.
    + apply sim_instr_a4.
    + apply sim_instr_a8.
Qed.

(* Print Assumptions riscv_test_safe. *)
