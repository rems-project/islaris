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

Require Export Sail.Base.
Require Export Sail.Prompt_monad.
Require Export Sail.MachineWord.
Require Export RV64.riscv_types.
Require Export Riscv_common.mem_metadata.
Require Export Riscv_common.riscv_extras.
Require Export RV64.riscv.

Local Arguments N.mul : simpl never.

Lemma regstate_eta (regs : regstate) :
  regs = {|
    satp := satp regs;
    tlb48 := tlb48 regs;
    tlb39 := tlb39 regs;
    htif_payload_writes := htif_payload_writes regs;
    htif_cmd_write := htif_cmd_write regs;
    htif_exit_code := htif_exit_code regs;
    htif_done := htif_done regs;
    htif_tohost := htif_tohost regs;
    mtimecmp := mtimecmp regs;
    fcsr := fcsr regs;
    f31 := f31 regs;
    f30 := f30 regs;
    f29 := f29 regs;
    f28 := f28 regs;
    f27 := f27 regs;
    f26 := f26 regs;
    f25 := f25 regs;
    f24 := f24 regs;
    f23 := f23 regs;
    f22 := f22 regs;
    f21 := f21 regs;
    f20 := f20 regs;
    f19 := f19 regs;
    f18 := f18 regs;
    f17 := f17 regs;
    f16 := f16 regs;
    f15 := f15 regs;
    f14 := f14 regs;
    f13 := f13 regs;
    f12 := f12 regs;
    f11 := f11 regs;
    f10 := f10 regs;
    f9 := f9 regs;
    f8 := f8 regs;
    f7 := f7 regs;
    f6 := f6 regs;
    f5 := f5 regs;
    f4 := f4 regs;
    f3 := f3 regs;
    f2 := f2 regs;
    f1 := f1 regs;
    f0 := f0 regs;
    float_fflags := float_fflags regs;
    float_result := float_result regs;
    utval := utval regs;
    ucause := ucause regs;
    uepc := uepc regs;
    uscratch := uscratch regs;
    utvec := utvec regs;
    vcsr := vcsr regs;
    vr31 := vr31 regs;
    vr30 := vr30 regs;
    vr29 := vr29 regs;
    vr28 := vr28 regs;
    vr27 := vr27 regs;
    vr26 := vr26 regs;
    vr25 := vr25 regs;
    vr24 := vr24 regs;
    vr23 := vr23 regs;
    vr22 := vr22 regs;
    vr21 := vr21 regs;
    vr20 := vr20 regs;
    vr19 := vr19 regs;
    vr18 := vr18 regs;
    vr17 := vr17 regs;
    vr16 := vr16 regs;
    vr15 := vr15 regs;
    vr14 := vr14 regs;
    vr13 := vr13 regs;
    vr12 := vr12 regs;
    vr11 := vr11 regs;
    vr10 := vr10 regs;
    vr9 := vr9 regs;
    vr8 := vr8 regs;
    vr7 := vr7 regs;
    vr6 := vr6 regs;
    vr5 := vr5 regs;
    vr4 := vr4 regs;
    vr3 := vr3 regs;
    vr2 := vr2 regs;
    vr1 := vr1 regs;
    vr0 := vr0 regs;
    pmpaddr15 := pmpaddr15 regs;
    pmpaddr14 := pmpaddr14 regs;
    pmpaddr13 := pmpaddr13 regs;
    pmpaddr12 := pmpaddr12 regs;
    pmpaddr11 := pmpaddr11 regs;
    pmpaddr10 := pmpaddr10 regs;
    pmpaddr9 := pmpaddr9 regs;
    pmpaddr8 := pmpaddr8 regs;
    pmpaddr7 := pmpaddr7 regs;
    pmpaddr6 := pmpaddr6 regs;
    pmpaddr5 := pmpaddr5 regs;
    pmpaddr4 := pmpaddr4 regs;
    pmpaddr3 := pmpaddr3 regs;
    pmpaddr2 := pmpaddr2 regs;
    pmpaddr1 := pmpaddr1 regs;
    pmpaddr0 := pmpaddr0 regs;
    pmp15cfg := pmp15cfg regs;
    pmp14cfg := pmp14cfg regs;
    pmp13cfg := pmp13cfg regs;
    pmp12cfg := pmp12cfg regs;
    pmp11cfg := pmp11cfg regs;
    pmp10cfg := pmp10cfg regs;
    pmp9cfg := pmp9cfg regs;
    pmp8cfg := pmp8cfg regs;
    pmp7cfg := pmp7cfg regs;
    pmp6cfg := pmp6cfg regs;
    pmp5cfg := pmp5cfg regs;
    pmp4cfg := pmp4cfg regs;
    pmp3cfg := pmp3cfg regs;
    pmp2cfg := pmp2cfg regs;
    pmp1cfg := pmp1cfg regs;
    pmp0cfg := pmp0cfg regs;
    vtype := vtype regs;
    vlenb := vlenb regs;
    vl := vl regs;
    vxrm := vxrm regs;
    vxsat := vxsat regs;
    vstart := vstart regs;
    senvcfg := senvcfg regs;
    menvcfg := menvcfg regs;
    tselect := tselect regs;
    stval := stval regs;
    scause := scause regs;
    sepc := sepc regs;
    sscratch := sscratch regs;
    stvec := stvec regs;
    sideleg := sideleg regs;
    sedeleg := sedeleg regs;
    mhartid := mhartid regs;
    marchid := marchid regs;
    mimpid := mimpid regs;
    mvendorid := mvendorid regs;
    minstret_increment := minstret_increment regs;
    minstret := minstret regs;
    mtime := mtime regs;
    mcycle := mcycle regs;
    mcountinhibit := mcountinhibit regs;
    scounteren := scounteren regs;
    mcounteren := mcounteren regs;
    mscratch := mscratch regs;
    mtval := mtval regs;
    mepc := mepc regs;
    mcause := mcause regs;
    mtvec := mtvec regs;
    medeleg := medeleg regs;
    mideleg := mideleg regs;
    mie := mie regs;
    mip := mip regs;
    mstatus := mstatus regs;
    mstatush := mstatush regs;
    misa := misa regs;
    cur_inst := cur_inst regs;
    cur_privilege := cur_privilege regs;
    x31 := x31 regs;
    x30 := x30 regs;
    x29 := x29 regs;
    x28 := x28 regs;
    x27 := x27 regs;
    x26 := x26 regs;
    x25 := x25 regs;
    x24 := x24 regs;
    x23 := x23 regs;
    x22 := x22 regs;
    x21 := x21 regs;
    x20 := x20 regs;
    x19 := x19 regs;
    x18 := x18 regs;
    x17 := x17 regs;
    x16 := x16 regs;
    x15 := x15 regs;
    x14 := x14 regs;
    x13 := x13 regs;
    x12 := x12 regs;
    x11 := x11 regs;
    x10 := x10 regs;
    x9 := x9 regs;
    x8 := x8 regs;
    x7 := x7 regs;
    x6 := x6 regs;
    x5 := x5 regs;
    x4 := x4 regs;
    x3 := x3 regs;
    x2 := x2 regs;
    x1 := x1 regs;
    instbits := instbits regs;
    nextPC := nextPC regs;
    PC := PC regs;
    vlen := vlen regs;
    elen := elen regs;
  |}.
Proof. now destruct regs. Qed.

Lemma x1_nextPC regs n:
  (x1 {[ regs with nextPC := n ]} ) = x1 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x2_nextPC regs n:
  (x2 {[ regs with nextPC := n ]} ) = x2 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x10_nextPC regs n:
  (x10 {[ regs with nextPC := n ]} ) = x10 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_x10 regs n:
  (nextPC {[ regs with x10 := n ]} ) = nextPC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x11_nextPC regs n:
  (x11 {[ regs with nextPC := n ]} ) = x11 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_x11 regs n:
  (nextPC {[ regs with x11 := n ]} ) = nextPC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x12_nextPC regs n:
  (x12 {[ regs with nextPC := n ]} ) = x12 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_x12 regs n:
  (nextPC {[ regs with x12 := n ]} ) = nextPC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x13_nextPC regs n:
  (x13 {[ regs with nextPC := n ]} ) = x13 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_x13 regs n:
  (nextPC {[ regs with x13 := n ]} ) = nextPC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma mstatus_nextPC regs n:
  (mstatus {[ regs with nextPC := n ]} ) = mstatus regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma misa_nextPC regs n:
  (misa {[ regs with nextPC := n ]} ) = misa regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma cur_privilege_nextPC regs n:
  (cur_privilege {[ regs with nextPC := n ]} ) = cur_privilege regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma PC_nextPC regs n:
  (PC {[ regs with nextPC := n ]} ) = PC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_nextPC regs n:
  (nextPC {[ regs with nextPC := n ]} ) = n.
Proof. now rewrite (regstate_eta regs). Qed.

(* This breaks the `with` notations so we have to import it later. *)
Require Import stdpp.unstable.bitvector_tactics.
Require Import isla.base.

Local Open Scope Z_scope.

(* This file should not depend on anything in islaris since it is quite slow to compile. *)

Lemma get_word_word_binop {n} f (b1 b2 : mword n):
  get_word (word_binop f b1 b2) = f _ (get_word b1) (get_word b2).
Proof. by destruct n. Qed.

Lemma get_word_to_word n (w : Word.word (Z.to_nat n)):
  get_word (to_word w) = w.
Proof. destruct n => //. Qed.

Lemma get_word_with_word n (b : mword n) f:
  (get_word (with_word (P:=id) f b)) = f (get_word b).
Proof. by destruct n. Qed.

Lemma get_word_inj n (m1 m2 : mword n):
  get_word m1 = get_word m2 → m1 = m2.
Proof. by destruct n. Qed.

Lemma get_word_mword_of_int n z:
  get_word (@mword_of_int n z) = Word.ZToWord (Z.to_nat n) z.
Proof. destruct n => //=. Qed.

Lemma Npow2_pow {n} : (2 ^ (N.of_nat n) = NatLib.Npow2 n)%N.
induction n.
* reflexivity.
* rewrite Nnat.Nat2N.inj_succ.
  rewrite N.pow_succ_r'.
  rewrite IHn.
  rewrite NatLib.Npow2_S.
  rewrite Word.Nmul_two.
  reflexivity.
Qed.

Lemma lt_Npow2 n n1:
  (0 ≤ n1)%Z →
  (n < NatLib.Npow2 (Z.to_nat n1))%N ↔ (Z.of_N n < 2 ^ n1)%Z.
Proof.
  move => ?.
  rewrite -Npow2_pow Z_nat_N. etrans; [ apply N2Z.inj_lt |].
  by rewrite N2Z.inj_pow Z2N.id.
Qed.

Lemma nth_error_lookup_some {A : Type} (l : list A) (i : nat) (x : A) :
  l !! i = Some x <-> List.nth_error l i = Some x.
split.
* move => H.
  have := (lookup_lt_Some _ _ _ H) => I.
  apply nth_lookup_Some with (d := x) in H.
  rewrite -H -nth_error_nth' //.
* move => H.
  destruct (l !! i) eqn:L.
  - apply nth_error_nth with (d:=x) in H.
    rewrite nth_lookup L in H.
    simpl in H.
    by subst.
  - apply lookup_ge_None_1 in L.
    have := nth_error_Some l i.
    rewrite H.
    intuition (congruence || lia).
Qed.

Lemma word_to_bools_lookup_Some n (w : Word.word n) (i : nat) x:
  (n > 0)%nat ->
  MachineWord.word_to_bools w !! i = Some x ↔ x = Z.testbit (Z.of_N (Word.wordToN w)) (n - S i)%nat ∧ (i < n)%nat.
move => ?.
rewrite nth_error_lookup_some MachineWord.word_to_bools_nth_Some //.
rewrite -nat_N_Z.
rewrite Z.testbit_of_N.
unfold MachineWord.word_to_N.
replace (N.of_nat (n - i -1)) with (N.of_nat (n - S i)) by lia.
done.
Qed.

Lemma wordToN_cast_word n m (b : Word.word n) (Heq : n = m):
  Word.wordToN (cast_nat b Heq) = Word.wordToN b.
Proof. destruct Heq. by rewrite cast_nat_refl. Qed.

Lemma wordToN_WS n b (w : Word.word n):
  (Z.of_N (Word.wordToN (Word.WS b w))) = Z.lor (bool_to_Z b) (Z.of_N (Word.wordToN w) ≪ 1).
Proof.
  simpl. destruct b.
  - rewrite N2Z.inj_succ. rewrite -Z.add_nocarry_lor /=.
    + rewrite Z.shiftl_mul_pow2; lia.
    + bitblast.
  - rewrite Z.lor_0_l Z.shiftl_mul_pow2 //. lia.
Qed.

Lemma wordToN_spec_high n i (w : Word.word n):
  n ≤ i →
  Z.testbit (Z.of_N (Word.wordToN w)) i = false.
Proof.
  move => ?.
  eapply Z.bounded_iff_bits_nonneg; [..|reflexivity] => //; try lia.
  move: w. have -> : n = Z.to_nat n by lia. move => w.
  have /lt_Npow2? := Word.wordToN_bound w.
  apply: Z.lt_le_trans; [naive_solver lia|].
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma bitblast_bounded_WordToN n (b : Word.word n):
  BitblastBounded (Z.of_N (Word.wordToN b)) (Z.of_nat n).
Proof.
  constructor. split; [lia|]. have := Word.wordToN_bound b.
  have {2}->: n = Z.to_nat (Z.of_nat n) by lia.
  move => /lt_Npow2. lia.
Qed.
Global Hint Resolve bitblast_bounded_WordToN | 15 : bitblast.
(* Also allow for terms where the Sail shim appears *)
Global Hint Unfold MachineWord.word : bitblast.

Lemma bitwp_spec f n (w1 w2 : Word.word n) z:
  f false false = false →
  0 ≤ z →
  Z.testbit (Z.of_N (Word.wordToN (Word.bitwp f w1 w2))) z =
    f (Z.testbit (Z.of_N (Word.wordToN w1)) z)
      (Z.testbit (Z.of_N (Word.wordToN w2)) z).
Proof.
  move => ?. elim: n w1 w2 z.
  - move => w1 w2 z ?. have -> := Word.shatter_word_0 w1. have -> := Word.shatter_word_0 w2.
    by rewrite /= Z.bits_0.
  - move => n IH w1 w2 z ?.
    have [b1 [? ->]] := Word.shatter_word_S w1. have [b2 [? ->]] := Word.shatter_word_S w2.
    cbn [Word.bitwp]. rewrite !wordToN_WS /=. bitblast. apply IH. lia.
Qed.

Lemma wordToN_wor n (w1 w2 : Word.word n):
  Z.of_N (Word.wordToN (Word.wor w1 w2)) = Z.lor (Z.of_N (Word.wordToN w1)) (Z.of_N (Word.wordToN w2)).
Proof. rewrite /Word.wor. bitblast. by rewrite bitwp_spec. Qed.

Lemma wordToN_wand n (w1 w2 : Word.word n):
  Z.of_N (Word.wordToN (Word.wand w1 w2)) = Z.land (Z.of_N (Word.wordToN w1)) (Z.of_N (Word.wordToN w2)).
Proof. rewrite /Word.wand. bitblast. by rewrite bitwp_spec. Qed.

Lemma wordToN_wnot n (w : Word.word n):
  Z.of_N (Word.wordToN (Word.wnot w)) = Z.land (Z.lnot (Z.of_N (Word.wordToN w))) (Z.ones n).
Proof.
  elim: w => //. move => b ?? IH.
  cbn [Word.wnot]. rewrite !wordToN_WS /= IH.
  bitblast.
Qed.

Lemma wordToN_wlshiftl n (w : Word.word n) (m : nat):
  Z.of_N (Word.wordToN w) < 2 ^ (n - m) →
  Z.of_N (Word.wordToN (Word.wlshift w m)) = (Z.of_N (Word.wordToN w)) ≪ m.
Proof.
  move => Hl.
  rewrite !Word.wordToN_nat Word.wordToNat_wlshift -!Word.wordToN_nat Z.shiftl_mul_pow2; [| lia].
  rewrite Nat2N.inj_mul Nat2N.inj_mod !Nat2N.inj_pow Nat2N.inj_sub -Word.wordToN_nat.
  destruct (decide (m ≤ n)). 2: {
    move: Hl. rewrite Z.pow_neg_r; lia.
  }
  rewrite N2Z.inj_mul N2Z.inj_mod !N2Z.inj_pow !N2Z.inj_sub; [|lia].
  rewrite Z.mod_small; lia.
Qed.

Lemma wordToN_setBit n (z : nat) (w : Word.word n) b:
  0 ≤ z →
  (z < n)%nat →
  Z.of_N (Word.wordToN (MachineWord.set_bit w z b)) =
    Z.lor (Z.land (Z.lnot (1 ≪ z)) (Z.of_N (Word.wordToN w))) (bool_to_Z b ≪ z).
Proof.
  unfold MachineWord.set_bit => ??. destruct n; [lia|].
  have H1 : Z.of_N (Word.wordToN (Word.natToWord (S n) 1)) = 1. {
    rewrite Word.wordToN_nat Word.wordToNat_natToWord_idempotent //.
    rewrite NatLib.Npow2_S. have := NatLib.Npow2_pos n. lia.
  }
  destruct b.
  - rewrite wordToN_wor wordToN_wand wordToN_wnot Word.wlshift_alt wordToN_wlshiftl H1. 2: {
      rewrite -(Z.succ_pred (_ - _)) Z.pow_succ_r; lia.
    }
    bitblast.
  - rewrite Z.shiftl_0_l Z.lor_0_r wordToN_wand wordToN_wnot Word.wlshift_alt wordToN_wlshiftl H1. 2: {
      rewrite -(Z.succ_pred (_ - _)) Z.pow_succ_r; lia.
    }
    bitblast.
Qed.

Lemma wlsb_testbit n (w : Word.word (S n)):
  Word.wlsb w = Z.testbit (Z.of_N (Word.wordToN w)) 0.
Proof.
  have [b [? ->]]:= Word.shatter_word_S w. simpl.
  rewrite Z.bit0_odd. by destruct b; rewrite ?N2Z.inj_succ ?Z.odd_succ N2Z.inj_mul ?Z.even_mul ?Z.odd_mul /=.
Qed.

Lemma wordToN_split1 sz1 sz2 (w : Word.word (sz1 + sz2)) :
  Word.wordToN (Word.split1 sz1 sz2 w) = (Word.wordToN w `mod` 2 ^ N.of_nat sz1)%N.
Proof. by rewrite !Word.wordToN_nat Word.wordToNat_split1 Nat2N.inj_mod Nat2N.inj_pow. Qed.

Lemma wordToN_split2 sz1 sz2 (w : Word.word (sz1 + sz2)) :
  Word.wordToN (Word.split2 sz1 sz2 w) = (Word.wordToN w `div` 2 ^ N.of_nat sz1)%N.
Proof. by rewrite !Word.wordToN_nat Word.wordToNat_split2 Nat2N.inj_div Nat2N.inj_pow. Qed.

Lemma wordToN_wrshift' n (w : Word.word n) z:
  Z.of_N (Word.wordToN (Word.wrshift' w z)) = Z.of_N (Word.wordToN w) ≫ z.
Proof.
  rewrite /Word.wrshift' wordToN_split2. destruct (PeanoNat.Nat.add_comm n z).
  rewrite DepEqNat.nat_cast_same Word.wordToN_combine Word.wordToN_wzero.
  rewrite Z.shiftr_div_pow2; [|lia].
  by rewrite N2Z.inj_div N2Z.inj_pow N.mul_0_r N.add_0_r nat_N_Z.
Qed.

Lemma getBit_testbit n z (w : Word.word n):
  (z < n)%nat →
  MachineWord.get_bit w z = Z.testbit (Z.of_N (Word.wordToN w)) (Z.of_nat z).
Proof. move => ?. rewrite MachineWord.word_to_N_get_bit // Z.testbit_of_N' /MachineWord.word_to_N -?Z_nat_N ?Nat2Z.id //.
apply Nat2Z.is_nonneg.
Qed.

Lemma bools_to_word_spec l (i : nat):
  Z.testbit (Z.of_N (Word.wordToN (MachineWord.bools_to_word l))) i = default false (rev l !! i).
Proof.
  rewrite -nat_N_Z Z.testbit_of_N -nth_lookup.
  destruct (lt_dec i (List.length l)) as [L|L].
  * rewrite rev_nth //.
    specialize (MachineWord.bools_to_word_nth_Some l (length l - S i)) as H.
    rewrite (nth_error_nth' _ false) in H. 2: lia.
    specialize (H (nth (length l - S i) l false)).
    destruct H as [H1].
    intuition.
    rewrite H1.
    f_equal.
    lia.
  * rewrite MachineWord.testbit_word_to_N_high; [|lia].
    rewrite nth_overflow // rev_length; lia.
Qed.

Lemma bit_to_bool_false b:
  b = B0 →
  bit_to_bool b = Done false.
Proof. by move => ->. Qed.
Lemma bit_to_bool_true b:
  b = B1 →
  bit_to_bool b = Done true.
Proof. by move => ->. Qed.
Lemma bitU_of_bool_B0 b :
  b = false →
  bitU_of_bool b = B0.
Proof. by move => ->. Qed.
Lemma bitU_of_bool_B1 b :
  b = true →
  bitU_of_bool b = B1.
Proof. by move => ->. Qed.
Lemma access_vec_dec_concrete x n (b : mword n) z:
  access_vec_dec b z = x →
  access_vec_dec b z = x.
Proof. by move => ->. Qed.

Lemma if_true b A (e1 e2 : A):
  b = true →
  (if b then e1 else e2) = e1.
Proof. naive_solver. Qed.
Lemma if_false b A (e1 e2 : A):
  b = false →
  (if b then e1 else e2) = e2.
Proof. naive_solver. Qed.

Lemma just_list_mapM {A} (l : list (option A)):
  just_list l = mapM (M := option) id l.
Proof. elim: l => //= -[|]//= ?? ->. case_match => //. Qed.

Lemma byte_chunks_reshape {A} n (l : list A):
  (length l = n * 8)%nat →
  byte_chunks l = Some (reshape (replicate n 8%nat) l).
Proof.
  move Hlen: (length l) => len.
  elim/lt_wf_ind: len l n Hlen => len IH l n ?. subst.
  destruct l => //=. { by destruct n. }
  do 7 (destruct l => /=; [lia|]). move => ?.
  have ?: (length l = ((n-1) * 8))%nat by lia.
  erewrite IH; [..|done]; [|simpl;lia|done].
  have {2}-> : (n = S (n-1)) by lia.
  by rewrite /= take_0 drop_0.
Qed.

Lemma cast_Z_id T m n x E : @cast_Z T m n x E = eq_rect m T x n E.
Proof. destruct E. apply cast_Z_refl. Qed.

Lemma length_bits_of_bytes l:
  (∀ x, x ∈ l → length x = 8%nat) →
  length (bits_of_bytes l) = (length l * 8)%nat.
Proof.
  move => Hf.
  rewrite /bits_of_bytes concat_join map_fmap join_length -list_fmap_compose /compose.
  rewrite (sum_list_fmap_same 8) //.
  apply list.Forall_forall => ?. rewrite /bits_of/= map_fmap fmap_length. apply: Hf.
Qed.

Lemma length_bits_of_mem_bytes l:
  (∀ x, x ∈ l → length x = 8%nat) →
  length (bits_of_mem_bytes l) = (length l * 8)%nat.
Proof.
  move => Hf. rewrite length_bits_of_bytes ?rev_length // => ?.
  rewrite rev_reverse elem_of_reverse. apply: Hf.
Qed.

Lemma bool_of_bitU_of_bool b:
  bool_of_bitU (bitU_of_bool b) = Some b.
Proof. by destruct b. Qed.


Lemma get_set_regval r regs regs' v:
  r ≠ "tlb48" ∧ r ≠ "tlb39" →
  set_regval r v regs = Some regs' ->
  get_regval r regs' = Some v.
Proof.
  move => [??].
  unfold set_regval, get_regval.
  have Hcase : ∀ s e1 e2 e1' e2',
      (r = s → e1 = Some regs' → e1' = Some v) →
      (e2 = Some regs' → e2' = Some v) →
      (if string_dec r s then e1 else e2) = Some regs' →
      (if string_dec r s then e1' else e2') = Some v. {
    move => s ??????. destruct (string_dec r s); eauto.
  }
  Time repeat (apply Hcase; [shelve|]). done.
  Unshelve.
  Time all: clear Hcase; move => ?; simpl; destruct v => //= ?; simplify_eq; try by destruct regs.
Qed.

Record register_ref_record := RegRef {
  reg_ref_type : Type;
  reg_ref_ref : register_ref regstate register_value reg_ref_type
}.
Arguments RegRef {_} _.

Definition riscv_regs := [
  ("satp", RegRef satp_ref);
  ("tlb48", RegRef tlb48_ref);
  ("tlb39", RegRef tlb39_ref);
  ("htif_payload_writes", RegRef htif_payload_writes_ref);
  ("htif_cmd_write", RegRef htif_cmd_write_ref);
  ("htif_exit_code", RegRef htif_exit_code_ref);
  ("htif_done", RegRef htif_done_ref);
  ("htif_tohost", RegRef htif_tohost_ref);
  ("mtimecmp", RegRef mtimecmp_ref);
  ("fcsr", RegRef fcsr_ref);
  ("f31", RegRef f31_ref);
  ("f30", RegRef f30_ref);
  ("f29", RegRef f29_ref);
  ("f28", RegRef f28_ref);
  ("f27", RegRef f27_ref);
  ("f26", RegRef f26_ref);
  ("f25", RegRef f25_ref);
  ("f24", RegRef f24_ref);
  ("f23", RegRef f23_ref);
  ("f22", RegRef f22_ref);
  ("f21", RegRef f21_ref);
  ("f20", RegRef f20_ref);
  ("f19", RegRef f19_ref);
  ("f18", RegRef f18_ref);
  ("f17", RegRef f17_ref);
  ("f16", RegRef f16_ref);
  ("f15", RegRef f15_ref);
  ("f14", RegRef f14_ref);
  ("f13", RegRef f13_ref);
  ("f12", RegRef f12_ref);
  ("f11", RegRef f11_ref);
  ("f10", RegRef f10_ref);
  ("f9", RegRef f9_ref);
  ("f8", RegRef f8_ref);
  ("f7", RegRef f7_ref);
  ("f6", RegRef f6_ref);
  ("f5", RegRef f5_ref);
  ("f4", RegRef f4_ref);
  ("f3", RegRef f3_ref);
  ("f2", RegRef f2_ref);
  ("f1", RegRef f1_ref);
  ("f0", RegRef f0_ref);
  ("float_fflags", RegRef float_fflags_ref);
  ("float_result", RegRef float_result_ref);
  ("utval", RegRef utval_ref);
  ("ucause", RegRef ucause_ref);
  ("uepc", RegRef uepc_ref);
  ("uscratch", RegRef uscratch_ref);
  ("utvec", RegRef utvec_ref);
  ("vcsr", RegRef vcsr_ref);
  ("vr31", RegRef vr31_ref);
  ("vr30", RegRef vr30_ref);
  ("vr29", RegRef vr29_ref);
  ("vr28", RegRef vr28_ref);
  ("vr27", RegRef vr27_ref);
  ("vr26", RegRef vr26_ref);
  ("vr25", RegRef vr25_ref);
  ("vr24", RegRef vr24_ref);
  ("vr23", RegRef vr23_ref);
  ("vr22", RegRef vr22_ref);
  ("vr21", RegRef vr21_ref);
  ("vr20", RegRef vr20_ref);
  ("vr19", RegRef vr19_ref);
  ("vr18", RegRef vr18_ref);
  ("vr17", RegRef vr17_ref);
  ("vr16", RegRef vr16_ref);
  ("vr15", RegRef vr15_ref);
  ("vr14", RegRef vr14_ref);
  ("vr13", RegRef vr13_ref);
  ("vr12", RegRef vr12_ref);
  ("vr11", RegRef vr11_ref);
  ("vr10", RegRef vr10_ref);
  ("vr9", RegRef vr9_ref);
  ("vr8", RegRef vr8_ref);
  ("vr7", RegRef vr7_ref);
  ("vr6", RegRef vr6_ref);
  ("vr5", RegRef vr5_ref);
  ("vr4", RegRef vr4_ref);
  ("vr3", RegRef vr3_ref);
  ("vr2", RegRef vr2_ref);
  ("vr1", RegRef vr1_ref);
  ("vr0", RegRef vr0_ref);
  ("pmpaddr15", RegRef pmpaddr15_ref);
  ("pmpaddr14", RegRef pmpaddr14_ref);
  ("pmpaddr13", RegRef pmpaddr13_ref);
  ("pmpaddr12", RegRef pmpaddr12_ref);
  ("pmpaddr11", RegRef pmpaddr11_ref);
  ("pmpaddr10", RegRef pmpaddr10_ref);
  ("pmpaddr9", RegRef pmpaddr9_ref);
  ("pmpaddr8", RegRef pmpaddr8_ref);
  ("pmpaddr7", RegRef pmpaddr7_ref);
  ("pmpaddr6", RegRef pmpaddr6_ref);
  ("pmpaddr5", RegRef pmpaddr5_ref);
  ("pmpaddr4", RegRef pmpaddr4_ref);
  ("pmpaddr3", RegRef pmpaddr3_ref);
  ("pmpaddr2", RegRef pmpaddr2_ref);
  ("pmpaddr1", RegRef pmpaddr1_ref);
  ("pmpaddr0", RegRef pmpaddr0_ref);
  ("pmp15cfg", RegRef pmp15cfg_ref);
  ("pmp14cfg", RegRef pmp14cfg_ref);
  ("pmp13cfg", RegRef pmp13cfg_ref);
  ("pmp12cfg", RegRef pmp12cfg_ref);
  ("pmp11cfg", RegRef pmp11cfg_ref);
  ("pmp10cfg", RegRef pmp10cfg_ref);
  ("pmp9cfg", RegRef pmp9cfg_ref);
  ("pmp8cfg", RegRef pmp8cfg_ref);
  ("pmp7cfg", RegRef pmp7cfg_ref);
  ("pmp6cfg", RegRef pmp6cfg_ref);
  ("pmp5cfg", RegRef pmp5cfg_ref);
  ("pmp4cfg", RegRef pmp4cfg_ref);
  ("pmp3cfg", RegRef pmp3cfg_ref);
  ("pmp2cfg", RegRef pmp2cfg_ref);
  ("pmp1cfg", RegRef pmp1cfg_ref);
  ("pmp0cfg", RegRef pmp0cfg_ref);
  ("vtype", RegRef vtype_ref);
  ("vlenb", RegRef vlenb_ref);
  ("vl", RegRef vl_ref);
  ("vxrm", RegRef vxrm_ref);
  ("vxsat", RegRef vxsat_ref);
  ("vstart", RegRef vstart_ref);
  ("senvcfg", RegRef senvcfg_ref);
  ("menvcfg", RegRef menvcfg_ref);
  ("tselect", RegRef tselect_ref);
  ("stval", RegRef stval_ref);
  ("scause", RegRef scause_ref);
  ("sepc", RegRef sepc_ref);
  ("sscratch", RegRef sscratch_ref);
  ("stvec", RegRef stvec_ref);
  ("sideleg", RegRef sideleg_ref);
  ("sedeleg", RegRef sedeleg_ref);
  ("mhartid", RegRef mhartid_ref);
  ("marchid", RegRef marchid_ref);
  ("mimpid", RegRef mimpid_ref);
  ("mvendorid", RegRef mvendorid_ref);
  ("minstret_increment", RegRef minstret_increment_ref);
  ("minstret", RegRef minstret_ref);
  ("mtime", RegRef mtime_ref);
  ("mcycle", RegRef mcycle_ref);
  ("mcountinhibit", RegRef mcountinhibit_ref);
  ("scounteren", RegRef scounteren_ref);
  ("mcounteren", RegRef mcounteren_ref);
  ("mscratch", RegRef mscratch_ref);
  ("mtval", RegRef mtval_ref);
  ("mepc", RegRef mepc_ref);
  ("mcause", RegRef mcause_ref);
  ("mtvec", RegRef mtvec_ref);
  ("medeleg", RegRef medeleg_ref);
  ("mideleg", RegRef mideleg_ref);
  ("mie", RegRef mie_ref);
  ("mip", RegRef mip_ref);
  ("mstatus", RegRef mstatus_ref);
  ("mstatush", RegRef mstatush_ref);
  ("misa", RegRef misa_ref);
  ("cur_inst", RegRef cur_inst_ref);
  ("cur_privilege", RegRef cur_privilege_ref);
  ("x31", RegRef x31_ref);
  ("x30", RegRef x30_ref);
  ("x29", RegRef x29_ref);
  ("x28", RegRef x28_ref);
  ("x27", RegRef x27_ref);
  ("x26", RegRef x26_ref);
  ("x25", RegRef x25_ref);
  ("x24", RegRef x24_ref);
  ("x23", RegRef x23_ref);
  ("x22", RegRef x22_ref);
  ("x21", RegRef x21_ref);
  ("x20", RegRef x20_ref);
  ("x19", RegRef x19_ref);
  ("x18", RegRef x18_ref);
  ("x17", RegRef x17_ref);
  ("x16", RegRef x16_ref);
  ("x15", RegRef x15_ref);
  ("x14", RegRef x14_ref);
  ("x13", RegRef x13_ref);
  ("x12", RegRef x12_ref);
  ("x11", RegRef x11_ref);
  ("x10", RegRef x10_ref);
  ("x9", RegRef x9_ref);
  ("x8", RegRef x8_ref);
  ("x7", RegRef x7_ref);
  ("x6", RegRef x6_ref);
  ("x5", RegRef x5_ref);
  ("x4", RegRef x4_ref);
  ("x3", RegRef x3_ref);
  ("x2", RegRef x2_ref);
  ("x1", RegRef x1_ref);
  ("instbits", RegRef instbits_ref);
  ("nextPC", RegRef nextPC_ref);
  ("PC", RegRef PC_ref);
  ("vlen", RegRef vlen_ref);
  ("elen", RegRef elen_ref)
].

Lemma get_regval_refs_eq r regs regs':
  (Forall (λ '(r', rf), r = r' → rf.(reg_ref_ref).(read_from) regs' = rf.(reg_ref_ref).(read_from) regs) riscv_regs) →
  get_regval r regs' = get_regval r regs.
Proof.
  unfold get_regval.
  have Hcase : ∀ s (e1 e2 e1' e2' : option register_value) rf' rfs,
      (read_from (reg_ref_ref rf') regs' = read_from (reg_ref_ref rf') regs → e1 = e1') →
      ((Forall (λ '(r', rf), r = r' → read_from (reg_ref_ref rf) regs' = read_from (reg_ref_ref rf) regs) rfs) → e2 = e2') →
      (Forall (λ '(r', rf), r = r' → read_from (reg_ref_ref rf) regs' = read_from (reg_ref_ref rf) regs) ((s, rf')::rfs)) →
      (if string_dec r s then e1 else e2) = (if string_dec r s then e1' else e2'). {
    move => s ?????? He1 He2 /(Forall_cons_1 _ _ _) [??]. destruct (string_dec r s); naive_solver.
  }
  repeat (apply Hcase; [ by destruct regs, regs' => -> |]). done.
Qed.

Lemma set_regval_refs_eq r regs regs' v:
  set_regval r v regs = Some regs' →
  ∃ rf v', (r, rf) ∈ riscv_regs ∧ regs' = rf.(reg_ref_ref).(write_to) v' regs.
Proof.
  have Hcase : ∀ s e1 e2 rf' rfs',
      (r = s → e1 = Some regs' → ∃ v', regs' = write_to (reg_ref_ref rf') v' regs) →
      (e2 = Some regs' → ∃ rf v', (r, rf) ∈ rfs' ∧ regs' = write_to (reg_ref_ref rf) v' regs) →
      (if string_dec r s then e1 else e2) = Some regs' →
      ∃ rf v', (r, rf) ∈ (s, rf')::rfs' ∧ regs' = write_to (reg_ref_ref rf) v' regs. {
    move => s ???? He1 He2. destruct (string_dec r s); set_solver.
  }
  repeat (apply Hcase; [ destruct v => //=; (try destruct o => //=) => ? Hx; injection Hx; by eexists _|]).
  done.
Qed.


Lemma get_set_regval_ne r r' regs regs' v:
  set_regval r' v regs = Some regs' →
  r ≠ r' →
  get_regval r regs' = get_regval r regs.
Proof.
  move => /set_regval_refs_eq[rf1 [? [Hin1 ->]]] Hneq.
  apply get_regval_refs_eq.
  have Hcase : ∀ a b (P : Prop) r rf (rfs : list (string * register_ref_record)),
      (a = r → b = rf → P) →
      ((a, b) ∈ rfs → P) →
      (a, b) ∈ (r, rf)::rfs → P. {
    move => ???????? /elem_of_cons[|]; naive_solver.
  }
  destruct regs.
  revert Hin1.
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 10 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  do 1 (apply Hcase; [abstract (move => ??; subst; repeat constructor; done)|]).
  by move =>/elem_of_nil.
Time Qed.

Lemma get_regval_None_stable r regs regs':
  get_regval r regs = None →
  get_regval r regs' = None.
Proof.
  have Hcase : ∀ s (e1 e2 e1' e2' : option register_value),
      (r = s → e1 = None → e1' = None) →
      (e2 = None → e2' = None) →
      (if string_dec r s then e1 else e2) = None →
      (if string_dec r s then e1' else e2') = None. {
    move => s ??????. destruct (string_dec r s); eauto.
  }
  repeat (apply Hcase; [done|]). done.
Qed.
