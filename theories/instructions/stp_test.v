Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.instructions.stp.

Definition start_address := [BV{64} (0x0000000010300000 - 0x4)].
Definition spec : list seq_label := [ SInstrTrap [BV{64} 0x0000000010300004] ].

Definition sys_regs `{!islaG Σ} `{!threadG} : iProp Σ :=
  ("SCTLR_EL2" ↦ᵣ Val_Bits [BV{64} 0x0000000004000002] ∗
  "SCR_EL3" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "TCR_EL2" ↦ᵣ Val_Bits [BV{64} 0] ∗
  "CFG_ID_AA64PFR0_EL1_EL0" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL1" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL2" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "CFG_ID_AA64PFR0_EL1_EL3" ↦ᵣ Val_Bits [BV{4} 1] ∗
  "OSLSR_EL1" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "OSDLR_EL1" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "EDSCR" ↦ᵣ Val_Bits [BV{32} 0] ∗
  "MPIDR_EL1" ↦ᵣ Val_Bits [BV{64} 0] ∗
  "PSTATE" ↦ᵣ (Val_Struct
          [("GE", Val_Poison); ("F", Val_Bits [BV{1} 1]);
          ("UAO", Val_Poison); ("C", Val_Bits [BV{1} 0]);
          ("SP", Val_Bits [BV{1} 1]); ("N", Val_Bits [BV{1} 0]);
          ("Q", Val_Poison); ("A", Val_Bits [BV{1} 1]); ("SS", Val_Bits [BV{1} 0]);
          ("E", Val_Poison); ("TCO", Val_Poison); ("I", Val_Bits [BV{1} 1]);
          ("PAN", Val_Poison); ("M", Val_Poison); ("D", Val_Bits [BV{1} 1]);
          ("nRW", Val_Bits [BV{1} 0]); ("EL", Val_Bits [BV{2} 2]);
          ("IT", Val_Poison); ("IL", Val_Bits [BV{1} 0]);
          ("Z", Val_Bits [BV{1} 0]); ("BTYPE", Val_Poison);
          ("SSBS", Val_Poison); ("T", Val_Poison); ("J", Val_Poison);
          ("V", Val_Bits [BV{1} 0]); ("DIT", Val_Bits [BV{1} 0])]))%I.

Definition cont_spec `{!islaG Σ} `{!threadG} a sp (v1 v2 : bv 64) : iProp Σ :=
  ∃ (vold1 vold2 : bv 64),
  "R0" ↦ᵣ Val_Bits v1 ∗
  "R1" ↦ᵣ Val_Bits v2 ∗
  (bv_sub sp [BV{64} 16]) ↦ₘ vold1 ∗
  (bv_sub sp [BV{64} 8]) ↦ₘ vold2 ∗
  (*⌜(bv_and sp [BV{64} 0xFFF0000000000000]) = [BV{64} 0]⌝ ∗ *)
  ⌜top_bits_zero 12 sp⌝ ∗
  "SP_EL2" ↦ᵣ Val_Bits sp ∗
  sys_regs ∗
  instr_pre a (
    "R0" ↦ᵣ Val_Bits v1 ∗
    "R1" ↦ᵣ Val_Bits v2 ∗
    "SP_EL2" ↦ᵣ Val_Bits (bv_sub sp [BV{64} 16])∗
    sys_regs ∗
    (bv_sub sp [BV{64} 16]) ↦ₘ v1 ∗
    (bv_sub sp [BV{64} 8]) ↦ₘ v2 ∗
    True).

Lemma mod_inj a b c d n (P1: a `mod` n = c `mod` n) (P2 : b `mod` n = d `mod` n) : (a + b) `mod` n = (c + d) `mod` n.
Proof.
  destruct (Z.eq_dec 0 n).
  + destruct e.
    by repeat rewrite Zmod_0_r.
  + rewrite (Z.add_mod a b); [|done].
    rewrite (Z.add_mod c d); [|done].
    by rewrite P1 P2.
Qed.

Lemma stp_wp `{!islaG Σ} `{!threadG} (sp v1 v2: bv 64):
  instr 0x0000000010300000 (Some [stp_trace]) -∗
  instr_body 0x0000000010300000 (cont_spec 0x0000000010300004 sp v1 v2).
Proof.
    iStartProof.
    unfold cont_spec, sys_regs.
    repeat liAStep; liShow.
    Unshelve.
    all: try done.
    all: try (repeat f_equal; unLET; bv_solve).
Qed.
