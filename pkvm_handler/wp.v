Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.pkvm.instrs.
Require Import isla.examples.sys_regs.

Definition instrs_iprop `{!islaG Σ} `{!threadG} := ([∗ list] i ∈ instr_map, instr i.1 (Some i.2))%I.

Definition spec_stp `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
    ∃ (vold1 vold2 : bv 64),
    "R0" ↦ᵣ Val_Bits v1 ∗
    "R1" ↦ᵣ Val_Bits v2 ∗
    (bv_sub sp [BV{64} 16]) ↦ₘ vold1 ∗
    (bv_sub sp [BV{64} 8]) ↦ₘ vold2 ∗
    ⌜bv_unsigned sp < 2 ^ 52⌝ ∗
    ⌜bv_unsigned sp > 16⌝ ∗
    "SP_EL2" ↦ᵣ Val_Bits sp ∗
    reg_col sys_regs ∗
    instr_pre a (
      "R0" ↦ᵣ Val_Bits v1 ∗
      "R1" ↦ᵣ Val_Bits v2 ∗
      "SP_EL2" ↦ᵣ Val_Bits (bv_sub sp [BV{64} 16])∗
      reg_col sys_regs ∗
      (bv_sub sp [BV{64} 16]) ↦ₘ v1 ∗
      (bv_sub sp [BV{64} 8]) ↦ₘ v2 ∗
      True).

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64) :
  instr 0x7400 (Some a7400) -∗
  instr_body 0x7400 (spec_stp 0x7404 sp v1 v2).
Proof.
  iStartProof.
  unfold spec_stp.
  unfold instrs_iprop.
  simpl.
  repeat liAStep; liShow.
  Unshelve.
  all: try (repeat f_equal; bv_solve).
Qed.

Definition exists_reg reg_name `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ v, reg_name ↦ᵣ v.

Definition spec_mrs `{!islaG Σ} `{!threadG} a (vold : bv 32) (v : bv 64) x : iProp Σ :=
  exists_reg "CPTR_EL2"  ∗
  exists_reg "CPTR_EL3" ∗
  exists_reg "CPACR_EL1" ∗
  exists_reg "CNTHCTL_EL2" ∗
  exists_reg "MDCR_EL2" ∗
  exists_reg "ICC_SRE_EL2" ∗
  exists_reg "CNTKCTL_EL1" ∗
  exists_reg "MPAM2_EL2" ∗
  exists_reg "MDCR_EL3" ∗
  exists_reg "ICH_HCR_EL2" ∗
  exists_reg "ICC_SRE_EL1_NS" ∗
  exists_reg "MPAMIDR_EL1" ∗
  exists_reg "PMUSERENR_EL0" ∗
  exists_reg "MPAM3_EL3" ∗
  exists_reg "ICC_SRE_EL3" ∗
  exists_reg "MPAMHCR_EL2" ∗
  exists_reg "HSTR_EL2" ∗
  reg_col sys_regs ∗
  exists_reg "R0" ∗
  "ESR_EL2" ↦ᵣ Val_Bits vold ∗
  ⌜bv_unsigned vold = x⌝ ∗
  ⌜bv_unsigned v = x⌝ ∗
  instr_pre a (
    reg_col sys_regs ∗
    "R0" ↦ᵣ Val_Bits v ∗
    True
  ).

Lemma mrs_wp `{!islaG Σ} `{!threadG} (vold: bv 32) (v : bv 64) x :
  instr 0x7404 (Some a7404) -∗
  instr_body 0x7404 (spec_mrs 0x7408 vold v x).
Proof.
  iStartProof.
  unfold spec_mrs.
  unfold instrs_iprop.
  unfold exists_reg.
  simpl.
  repeat liAStep; liShow.
  Unshelve.
  (* TODO: Check if bv_solve on the latest branch solves this, otherwise fix it *)
  repeat f_equal. unLET.
  autorewrite with bv_simplify.
  apply bv_eq.
  autorewrite with bv_unfold.
  auto. 
Qed.

Definition spec_lsr `{!islaG Σ} `{!threadG} a (v vold : bv 64) : iProp Σ :=
  "R0" ↦ᵣ Val_Bits vold ∗
  ⌜bv_unsigned v = Z.shiftr (bv_unsigned vold) 26⌝ ∗
  reg_col sys_regs ∗
  instr_pre a (
    reg_col sys_regs ∗
    "R0" ↦ᵣ Val_Bits v ∗
    True
  ).

Definition bv_unsigned_land {n} (v : bv n) := Z.land (bv_unsigned v) (Z.ones (Z.of_N n)).

Lemma bv_and_ones {n} (v : bv n) : bv_unsigned v = bv_unsigned_land v.
Proof.
  unfold bv_unsigned_land.
  rewrite Z.land_ones; [|lia].
  symmetry.
  apply Z.mod_small.
  destruct v as [x wf].
  unfold bitvector.bv_wf, bv_modulus in wf.
  unfold bv_unsigned.
  lia.
Qed.

Ltac onesify n :=
  lazymatch n with
  | O => idtac
  | S ?n' => 
    let m := eval vm_compute in (Z.of_nat n) in
    let x := eval vm_compute in (Z.ones m) in
    change x with (Z.ones m);
    onesify n'
  end.

Hint Rewrite
  Z.bits_0
  Z.lor_0_l Z.lor_0_r
  Z.land_spec Z.lor_spec
  andb_false_l andb_false_r andb_true_l andb_true_r
  orb_false_l orb_false_r orb_true_l orb_true_r : bits_simplify.

Hint Rewrite
  Z_ones_spec Z.testbit_neg_r Z.shiftl_spec Z.shiftr_spec using lia : bits_simplify.

Ltac bits_solve :=
  onesify (64%nat);
  rewrite <- Z.land_ones; [|lia];
  repeat match goal with b : bv _ |- _ => match goal with G : bv_unsigned b = _ |- _ => rewrite G; clear G end end;
  repeat match goal with B : bv ?n |- _ => rewrite !(bv_and_ones B) end; unfold bv_unsigned_land;
  apply Z.bits_inj_iff';
  intros n Hn;
  autorewrite with bits_simplify;
  repeat match goal with 
  |- context [bool_decide (?a < ?b)] => 
    destruct (Z.lt_ge_cases a b);
    [rewrite !(bool_decide_eq_true_2 (a < b))| rewrite !(bool_decide_eq_false_2 (a < b))]; try lia
  end;
  autorewrite with bits_simplify;
  repeat (match goal with |- context [Z.testbit _ ?a] => idtac a; rewrite (Z.testbit_neg_r _ a); idtac a; [|lia] end);
  (* Concievably you might want to try bv_solve or bitblast here *)
  by autorewrite with bits_simplify.

Lemma lsr_wp `{!islaG Σ} `{!threadG} (v vold : bv 64):
  instr 0x7408 (Some a7408) -∗
  instr_body 0x7408 (spec_lsr 0x740c v vold).
Proof.
  iStartProof.
  unfold spec_lsr.
  repeat liAStep; liShow.
  Unshelve.
  repeat f_equal. unLET.
  apply bv_eq.
  autorewrite with bv_unfold.
  unfold bv_wrap in *.
  bits_solve.
Qed.
