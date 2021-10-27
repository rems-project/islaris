Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail_riscv.sail_opsem.
Require Import isla.sail_riscv.tactics.
Require Import isla.automation.
Require Import isla.riscv64.riscv64.
From isla.instructions.riscv64_test Require Import instrs.
Require Import isla.examples.riscv64_test.

Lemma sim_instr_a0:
  sim_instr (Uncompressed [BV{32} 0x00000513]) a0.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
  - rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a4:
  sim_instr (Uncompressed [BV{32} 0x00150513]) a4.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_ITYPE. red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite mword_to_bv_add_vec //.
Qed.

Lemma sim_instr_a8:
  sim_instr (Uncompressed [BV{32} 0x00b13423]) a8.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_STORE. red_sim. rewrite x2_nextPC.
  unfold check_misaligned. rewrite Hassume0.
  repeat (rewrite (access_vec_dec_concrete B0); [|shelve]).
  red_sim.
  unfold translateAddr. red_sim.
  unfold effectivePrivilege. red_sim.
  rewrite mstatus_nextPC.
  have -> : (_get_Mstatus_MPRV (mstatus regs)) = ('b "0") by shelve.
  red_sim.
  unfold translateAddr_priv. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold translationMode. rewrite cur_privilege_nextPC.
  have -> : (cur_privilege regs) = Machine by shelve. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x11_nextPC.
  unfold mem_write_value, mem_write_value_meta. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold effectivePrivilege. red_sim. rewrite mstatus_nextPC.
  have -> : (_get_Mstatus_MPRV (mstatus regs)) = ('b "0") by shelve.
  red_sim. rewrite Hassume. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  all: rewrite -?Hassume1 -?Hassume2 -?Hassume3 -?Hassume4 -?Hassume5 -?Hassume6 -?Hassume7 //.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - rewrite Hassume9. by apply bv_neq.
  - admit.
  - admit.
  - rewrite Hassume9. by apply bv_neq.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma sim_instr_ac:
  sim_instr (Uncompressed [BV{32} 0x00813583]) ac.
Proof.
  move => regs. eexists _. split; [by left|].
  unfold step_cpu. red_sim. unfold execute. red_sim.
  unfold execute_LOAD. red_sim.
  unfold check_misaligned. rewrite Hassume0.
  repeat (rewrite (access_vec_dec_concrete B0); [|shelve]).
  red_sim.
  unfold translateAddr. red_sim.
  unfold effectivePrivilege. red_sim.
  rewrite mstatus_nextPC.
  have -> : (_get_Mstatus_MPRV (mstatus regs)) = ('b "0") by shelve.
  red_sim.
  unfold translateAddr_priv. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold translationMode. rewrite cur_privilege_nextPC.
  have -> : (cur_privilege regs) = Machine by shelve. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim. rewrite x2_nextPC.
  unfold mem_read. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  apply: sim_read_reg_l; [done|]. red_sim.
  unfold effectivePrivilege. red_sim. rewrite mstatus_nextPC.
  have -> : (_get_Mstatus_MPRV (mstatus regs)) = ('b "0") by shelve.
  red_sim.
  have -> : plat_enable_pmp () = false by simplify_eq. red_sim.
  rewrite if_false; [|shelve]. rewrite if_true; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
Admitted.

Lemma sim_instr_a10:
  sim_instr (Uncompressed [BV{32} 0x00b50463]) a10.
Proof.
  move => regs.
  destruct (eq_vec (x10 regs) (x11 regs)) eqn: Hb1; sim_simpl_hyp Hb1.
  all: eexists _; split. 1: by left. 2: by right; left.
  all: unfold step_cpu; red_sim; unfold execute; red_sim.
  all: unfold execute_BTYPE; red_sim.
  all: apply: sim_read_reg_l; [done|]; red_sim.
  all: rewrite x10_nextPC x11_nextPC Hb1; red_sim.
  rewrite bit_to_bool_false; [|shelve]. red_sim.
  Unshelve. all: sim_simpl_goal.
  - rewrite (eq_vec_to_bv 64) // bool_decide_eq_true in Hb1. by rewrite Hb1.
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
  - rewrite (eq_vec_to_bv 64) // bool_decide_eq_false in Hb1. done.
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
  <[ [BV{64} 0x0000000010300008] := Uncompressed [BV{32} 0x00b13423]]> $
  <[ [BV{64} 0x000000001030000c] := Uncompressed [BV{32} 0x00813583]]> $
  <[ [BV{64} 0x0000000010300010] := Uncompressed [BV{32} 0x00b50463]]> $
  ∅.

Definition riscv_test_initial_sail_state (x2v : bv 64) (regs : regstate) : sail_state :=
  SAIL (Done tt) regs (riscv_test_state_global x2v).(seq_mem) riscv_test_sail_instrs false.

Lemma riscv_test_safe regs (satpv x10v x2v mstatus_bits x11v : bv 64):
  plat_enable_pmp () = false →
  plat_enable_misaligned_access () = false →
  mword_to_bv (plat_ram_base ()) = [BV{64} 0x0000000080000000] →
  mword_to_bv (plat_ram_size ()) = [BV{64} 0x0000000004000000] →
  mword_to_bv (plat_rom_base ()) = [BV{64} 0x0000000000001000] →
  mword_to_bv (plat_rom_size ()) = [BV{64} 0x0000000000000100] →
  mword_to_bv (plat_clint_base ()) = [BV{64} 0x0000000002000000] →
  mword_to_bv (plat_clint_size ()) = [BV{64} 0x00000000000c0000] →
  mword_to_bv (plat_htif_tohost ()) = [BV{64} 0x0000000040001000] →
  bv_extract 17 1 mstatus_bits = [BV{1} 0] →
  bv_unsigned x2v `mod` 8 = 0 →
  0x0000000080000000 ≤ bv_unsigned x2v + 8 < 0x0000000080000000 + 0x0000000004000000 →
  PC regs = bv_to_mword [BV{64} 0x0000000010300000] →
  x2 regs = bv_to_mword x2v →
  x10 regs = bv_to_mword x10v →
  x11 regs = bv_to_mword x11v →
  satp regs = bv_to_mword satpv →
  cur_privilege regs = Machine →
  misa regs = {| Misa_Misa_chunk_0 := bv_to_mword misa_bits |} →
  mstatus regs = {| Mstatus_Mstatus_chunk_0 := bv_to_mword mstatus_bits |} →
  safe sail_module (riscv_test_initial_sail_state x2v regs) ∧
    (∀ κs σ', steps sail_module (riscv_test_initial_sail_state x2v regs) κs σ' → riscv_test_spec x11v κs).
Proof.
  move => ????????? ??? HPC Hx2 Hx10 Hx11 Hsatp Hcur_priv Hmisa Hmstatus.
  apply: iris_transfer_refines.
  { apply iris_module_wf_isla_lang. }
  { move => ????. by apply (riscv_test_adequate mstatus_bits satpv x2v x10v x11v). }
  eapply sim_implies_refines.
  - rewrite !dom_insert_L !dom_empty_L. set_solver.
  - move => ??.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq => //.
    all: unfold get_regval_or_config; simpl; eexists _; split; [done|]; sim_simpl_goal.
    + by rewrite HPC.
    + by rewrite Hx2 mword_to_bv_to_mword.
    + by rewrite Hx10 mword_to_bv_to_mword.
    + by rewrite Hx11 mword_to_bv_to_mword.
    + by rewrite Hcur_priv.
    + by rewrite Hmisa.
    + by rewrite Hmstatus mword_to_bv_to_mword.
    + by rewrite Hsatp mword_to_bv_to_mword.
  - done.
  - unfold riscv_test_sail_instrs. move => ??? Hsail.
    repeat move => /lookup_insert_Some[[??]|[? ]]; simplify_map_eq.
    + apply sim_instr_a0.
    + apply sim_instr_a4.
    + apply sim_instr_a8.
    + apply sim_instr_ac.
    + apply sim_instr_a10.
Qed.

(* Print Assumptions riscv_test_safe. *)
