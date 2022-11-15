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

Require Export isla.sail_riscv.base.
Require Export isla.sail_riscv.RV64.
Require Export isla.opsem.
Require Import isla.adequacy.
Require Import isla.riscv64.arch.

(*** Relating values *)
Definition byte_to_memory_byte (b : byte) : memory_byte :=
  bitU_of_bool <$> rev (bv_to_bits b).

Global Instance bitU_of_bool_inj : Inj eq eq bitU_of_bool.
Proof. move => [] []; done. Qed.

Global Instance byte_to_memory_byte_inj : Inj eq eq byte_to_memory_byte.
Proof.
  move => x y. rewrite /byte_to_memory_byte/= => ?. simplify_list_eq. unfold byte in *.
  apply bv_eq. bitblast as n.
  destruct (decide (n = 0)); subst => //.
  destruct (decide (n = 1)); subst => //.
  destruct (decide (n = 2)); subst => //.
  destruct (decide (n = 3)); subst => //.
  destruct (decide (n = 4)); subst => //.
  destruct (decide (n = 5)); subst => //.
  destruct (decide (n = 6)); subst => //.
  destruct (decide (n = 7)); subst => //.
  lia.
Qed.

Lemma byte_to_memory_byte_length b: length (byte_to_memory_byte b) = 8%nat.
Proof. done. Qed.

Local Transparent bv_to_bits.
Lemma byte_to_memory_byte_lookup_Some b i x:
  byte_to_memory_byte b !! i = Some x ↔ (i < 8)%nat ∧ x = bitU_of_bool (Z.testbit (bv_unsigned b) (7 - i)%nat).
Proof. do 8 try destruct i => //=; naive_solver lia. Qed.

Definition bv_to_mword {n1 n2} (b : bv n1) : mword n2 :=
  word_to_mword (Word.NToWord _ (Z.to_N $ bv_unsigned b)).
Arguments bv_to_mword : simpl never.
Definition mword_to_bv {n1 n2} (b : mword n1) : bv n2 :=
  default (bv_0 _) (Z_to_bv_checked _ (Z.of_N $ Word.wordToN (get_word b))).
Arguments mword_to_bv : simpl never.

Lemma mword_to_bv_unsigned {n1 n2} (b : mword n1):
  n1 = Z.of_N n2 →
  bv_unsigned (mword_to_bv (n2:=n2) b) = Z.of_N (Word.wordToN (get_word b)).
Proof.
  move => Heq. rewrite /mword_to_bv/Z_to_bv_checked. case_option_guard as Hn => //=.
  contradict Hn. apply/bv_wf_in_range. unfold bv_modulus.
  have /lt_Npow2:= Word.wordToN_bound (get_word b). subst. lia.
Qed.

Lemma mword_to_bv_signed {n1 n2} (b : mword n1):
  n1 = Z.of_N n2 →
  bv_signed (mword_to_bv (n2:=n2) b) = Word.wordToZ (get_word b).
Proof.
  move => Heq.
  rewrite /bv_signed mword_to_bv_unsigned // Word.wordToZ_wordToN /bv_swrap.
  move: (get_word b) => {}b.
  destruct (Z.to_nat n1) eqn:?.
  { rewrite (Word.shatter_word_0 b) /=. have -> : n2 = 0%N by lia. done. }
  case_match as Hwmsb.
  - move: Hwmsb => /Word.wmsb_true_bound.
    rewrite -Npow2_pow. have {1}-> : N.of_nat n = Z.to_N (n1 - 1) by lia.
    move => /N2Z.inj_le. rewrite N2Z.inj_pow Z2N.id ?ZLib.pow2_div2; [|lia..] => ?.
    rewrite /bv_wrap (Z.mod_in_range 1).
    + rewrite /bv_modulus -Npow2_pow N2Z.inj_pow.
      have -> : N.of_nat (S n) = n2 by lia.
      lia.
    + rewrite -bv_half_modulus_twice; [|lia].
      rewrite /bv_half_modulus /bv_modulus.
      have -> : Z.of_N n2 = n1 by lia.
      have := Word.wordToN_bound b.
      have {2}->: (S n) = Z.to_nat n1 by lia.
      move => /lt_Npow2 ?.
      split; try lia.
      suff : Z.of_N (Word.wordToN b) < (2 ^ n1 `div` 2 + 2 ^ n1 `div` 2) by lia.
      rewrite Z.add_diag -Z_div_exact_2 //. 1: lia.
      rewrite Zpow_facts.Zpower_mod // Z.pow_0_l' //. lia.
  - move: Hwmsb => /Word.wmsb_false_bound.
    have {2}-> : n = Z.to_nat (n1 - 1) by lia. move => /lt_Npow2.
    rewrite ZLib.pow2_div2; [|lia] => ?. rewrite bv_wrap_small; [lia|].
    rewrite -bv_half_modulus_twice; [|lia].
    rewrite /bv_half_modulus /bv_modulus.
    have {3}-> : Z.of_N n2 = n1 by lia.
    lia.
Qed.

Lemma mword_to_bv_to_mword {n1 n2} (b : bv n1) :
  n2 = Z.of_N n1 →
  (@mword_to_bv n2 n1 (bv_to_mword b)) = b.
Proof.
  move => Heq. apply bv_eq. rewrite mword_to_bv_unsigned //.
  rewrite /bv_to_mword/word_to_mword get_word_to_word Word.wordToN_NToWord_2.
  - bv_saturate. lia.
  - apply/lt_Npow2; [lia|]. bv_saturate. unfold bv_modulus in *. rewrite Heq. lia.
Qed.

Lemma uint_plain_to_bv_unsigned n (b : mword n) :
  0 ≤ n →
  uint b = bv_unsigned (mword_to_bv (n2:=Z.to_N n) b).
Proof. move => ?. rewrite mword_to_bv_unsigned //. lia. Qed.

Lemma eq_vec_to_bv n1 {n2} (b1 b2 : mword n2) :
  n2 = Z.of_N n1 →
  eq_vec b1 b2 = (bool_decide (mword_to_bv b1 =@{bv n1} mword_to_bv b2)).
Proof.
  move => Heq.
  case_bool_decide as Hb.
  - apply Word.weqb_eq. move: Hb => /bv_eq.
    by rewrite !mword_to_bv_unsigned // => /N2Z.inj/Word.wordToN_inj.
  - apply Word.weqb_ne. contradict Hb. apply bv_eq.
    by rewrite !mword_to_bv_unsigned // Hb.
Qed.

Lemma mword_to_bv_subrange_vec_dec z1 z2 n2 n1 (b : mword n1):
  0 <= z2 ->
  z2 <= z1 < n1 ->
  (∀ b Heq, Word.wordToN (get_word (@cast_to_mword (Z.to_nat z1 - Z.to_nat z2 + 1) (z1 - z2 + 1) b Heq)) = Word.wordToN b) → (* TODO: remove this once there is a proof of wordToN_get_word_cast_to_mword *)
  n1 = Z.of_N n2 →
  mword_to_bv (subrange_vec_dec b z1 z2) =
    bv_extract (Z.to_N z2) (Z.to_N (z1 + 1 - z2)) (mword_to_bv (n2:=n2) b).
Proof.
  move => Hz2 Hz1 Hx ?.
  unfold subrange_vec_dec.  destruct (sumbool_of_bool _); [|lia].
  unfold subrange_vec_dec_precise. apply bv_eq.
  rewrite bv_extract_unsigned !mword_to_bv_unsigned; [|lia..].
  rewrite Hx wordToN_split2 wordToN_cast_word wordToN_split1 wordToN_cast_word.
  rewrite !Z_nat_N !Z2N.id ?N2Z.inj_div ?N2Z.inj_mod ?N2Z.inj_pow ?Z2N.id; [|lia..].
  have -> : Z.of_N (N.of_nat (Z.to_nat z1 + 1)) = z1 + 1 by lia.
  rewrite -Z.shiftr_div_pow2 -?Z.land_ones; [|lia..].
  bitblast.
Qed.

Lemma getBit_get_word_testbit n z (w : mword n):
  (0 < n) →
  getBit (get_word w) z = Z.testbit (bv_unsigned (mword_to_bv (n2:=Z.to_N n) w)) (Z.of_nat z).
Proof. etrans; [apply getBit_testbit|]; [lia|]. rewrite mword_to_bv_unsigned //. lia. Qed.

Lemma access_vec_dec_to_bv  n1 (b : mword n1) z :
  0 ≤ z →
  0 < n1 →
  access_vec_dec b z = bitU_of_bool (Z.testbit (bv_unsigned (mword_to_bv (n2:=Z.to_N n1) b)) z).
Proof.
  move => ??. rewrite /access_vec_dec/access_mword_dec. f_equal. rewrite getBit_get_word_testbit => //.
  f_equal. lia.
Qed.

Lemma bitlistFromWord_to_bv n1 n2 (v : mword n1):
  n1 = Z.of_N n2 →
  bitlistFromWord (get_word v) = rev (bv_to_bits (mword_to_bv (n2:=n2) v)).
Proof.
  move => ?.
  apply: list_eq_same_length; [done| |].
  { rewrite rev_length length_bitlistFromWord bv_to_bits_length; lia. }
  move => ????. rewrite bitlistFromWord_lookup_Some -(mword_to_bv_unsigned (n2:=n2)) // rev_reverse => -[??].
  move => /reverse_lookup_Some[/bv_to_bits_lookup_Some[??] ?]. simplify_eq.
  rewrite bv_to_bits_length. f_equal. lia.
Qed.

Lemma mword_to_bv_add_vec {n1 : Z} {n2 : N} (b1 b2 : mword n1) :
  n1 = Z.of_N n2 →
  mword_to_bv (n2:=n2) (add_vec b1 b2) = bv_add (mword_to_bv b1) (mword_to_bv b2).
Proof.
  move => Hn. apply bv_eq.
  rewrite bv_add_unsigned !mword_to_bv_unsigned // get_word_word_binop.
  rewrite /Word.wplus /Word.wordBin Word.wordToN_NToWord_eqn.
  rewrite /bv_wrap/bv_modulus -(N2Z.inj_pow 2) -Npow2_pow Z_nat_N.
  rewrite N2Z.inj_mod N2Z.inj_add. f_equal. by rewrite Hn N2Z.id.
Qed.
Arguments add_vec : simpl never.

Lemma mword_to_bv_add_vec_int n1 n2 (b : mword n1) z:
  0 ≤ z → (* not strictly necessary but makes the proof easier *)
  n1 = Z.of_N n2 →
  mword_to_bv (n2:=n2) (add_vec_int b z) = bv_add_Z (mword_to_bv b) z.
Proof.
  move => ??.
  rewrite /add_vec_int mword_to_bv_add_vec //.
  apply bv_eq.
  rewrite bv_add_unsigned bv_add_Z_unsigned.
  rewrite -(bv_wrap_add_idemp_r _ _ z).
  f_equal. f_equal.
  rewrite mword_to_bv_unsigned // get_word_mword_of_int.
  rewrite -Word.NToWord_Z_to_N // Word.wordToN_NToWord_eqn -Npow2_pow Z_nat_N.
  rewrite N2Z.inj_mod N2Z.inj_pow !Z2N.id; [|lia..].
  unfold bv_wrap, bv_modulus in *.
  do 2 f_equal. done.
Qed.

Lemma mword_to_bv_EXTS n1 n2' n2 (b : mword n1):
  (∀ b, Word.wordToZ (get_word (@fit_word (Z.to_nat n1 + Z.to_nat (n2' - n1)) n2' b)) = Word.wordToZ b) → (* TODO: remove this once there is a proof of wordToZ_get_word_cast_to_mword *)
  0 ≤ n1 →
  n2' = Z.of_N n2 →
  n1 ≤ n2' →
  mword_to_bv (n2:=n2) (@EXTS _ n2' b) = bv_sign_extend _ (mword_to_bv (n2:=(Z.to_N n1)) b).
Proof.
  move => Hx ???.
  apply bv_eq_signed. rewrite mword_to_bv_signed //. rewrite /EXTS/sign_extend/exts_vec/= Hx.
  rewrite Word.sext_wordToZ bv_sign_extend_signed ?mword_to_bv_signed //.
  all: lia.
Qed.
Arguments EXTS : simpl never.

(* #[local] Hint Rewrite wordToN_spec_high Z_of_bool_spec_high using lia : rewrite_bits_db. *)
Lemma mword_to_bv_update_vec_dec n1 n2 (b : mword n1) b1 z b2:
  bool_of_bitU b1 = Some b2 →
  n1 = Z.of_N n2 →
  z < n1 →
  0 ≤ z →
  mword_to_bv (n2:=n2) (update_vec_dec b z b1) = bv_or
    (bv_and (bv_not (Z_to_bv n2 (1 ≪ z))) (mword_to_bv b))
    (Z_to_bv n2 (bool_to_Z b2 ≪ z)).
Proof.
  move => Hb ???.
  apply bv_eq. rewrite mword_to_bv_unsigned //.
  rewrite /update_vec_dec/opt_def /update_mword_dec Hb.
  rewrite /update_mword_bool_dec get_word_with_word wordToN_setBit;[|lia..].
  rewrite bv_or_unsigned bv_and_unsigned bv_not_unsigned !Z_to_bv_unsigned mword_to_bv_unsigned//.
  rewrite Z2Nat.id; [|lia]. rewrite !bv_wrap_land.
  bitblast.
Qed.

Lemma mem_bytes_of_bits_to_bv n (v : mword n) len:
  n = 8 * len →
  0 <= n →
  mem_bytes_of_bits v = Some (byte_to_memory_byte <$>
       (bv_to_little_endian len 8 (@bv_unsigned (Z.to_N n) (mword_to_bv v)))).
Proof.
  move => Hn ?.
  rewrite /mem_bytes_of_bits/bytes_of_bits/bits_of/= option_map_fmap map_fmap.
  apply fmap_Some. eexists (rev _). rewrite rev_involutive. split; [|done].
  rewrite (byte_chunks_reshape (Z.to_nat len)).
  2: { rewrite fmap_length length_bitlistFromWord. lia. }
  f_equal. eapply list_eq_same_length; [done | |].
  { rewrite reshape_length rev_length replicate_length fmap_length bv_to_little_endian_length; lia. }
  move => i x y ?. rewrite rev_reverse sublist_lookup_reshape; [|lia|].
  2: { rewrite fmap_length length_bitlistFromWord. lia. }
  move => /sublist_lookup_Some'[??] /reverse_lookup_Some.
  rewrite list_lookup_fmap fmap_length bv_to_little_endian_length; [|lia] => -[Hl ?].
  move: Hl => /fmap_Some[?[/bv_to_little_endian_lookup_Some[|???]]]; [lia|]. simplify_eq.
  apply: list_eq_same_length; [done|..].
  { rewrite byte_to_memory_byte_length take_length_le ?drop_length; lia. }
  move => i' x y ? /lookup_take_Some. rewrite lookup_drop list_lookup_fmap.
  move => [/fmap_Some[?[/bitlistFromWord_lookup_Some[??]?]]?] /byte_to_memory_byte_lookup_Some[??].
  simplify_eq. f_equal.
  rewrite -(mword_to_bv_unsigned (n2:=(Z.to_N (8 * len)))); [|lia].
  rewrite Z_to_bv_unsigned bv_wrap_spec_low ?Z.shiftr_spec; [|lia..].
  f_equal. lia.
Qed.

Lemma just_list_bits_of_mem_bytes bs:
  just_list (bool_of_bitU <$> bits_of_mem_bytes (byte_to_memory_byte <$> bs)) =
    Some (mjoin (((λ x, reverse (bv_to_bits x)) <$> reverse bs))).
Proof.
  rewrite just_list_mapM. apply mapM_Some_2. apply Forall2_same_length_lookup_2. {
    rewrite fmap_length join_length -list_fmap_compose /compose /= sum_list_fmap_const.
    rewrite length_bits_of_mem_bytes ?fmap_length ?reverse_length //.
    move => ? /elem_of_list_fmap[?[??]]. subst. by rewrite byte_to_memory_byte_length.
  }
  move => i x y. rewrite list_lookup_fmap /bits_of_mem_bytes/bits_of_bytes concat_join map_fmap.
  move => /fmap_Some[?[/(join_lookup_Some_same_length 8)[|?[?[?[Hm [Hl ?]]]]]]].
  { apply list.Forall_forall => ?. rewrite rev_reverse. move => /elem_of_list_fmap[?[? /elem_of_reverse /elem_of_list_fmap[?[??]]]]; subst. done. }
  move => ?. subst. move: Hm. rewrite list_lookup_fmap rev_reverse. move => /fmap_Some [?[Hrev ?]]. subst.
  move: Hl. rewrite /bits_of /= map_fmap list_lookup_fmap => /fmap_Some [?[Hl ?]]. subst.
  move: Hrev => /reverse_lookup_Some. rewrite list_lookup_fmap => -[/fmap_Some[?[Hbs ?]] ?]. subst.
  move: Hl => /byte_to_memory_byte_lookup_Some[??].
  move => /join_lookup_Some_same_length'[| |].
  { apply list.Forall_forall => ? /elem_of_list_fmap[?[??]]. subst. by rewrite reverse_length bv_to_bits_length. }
  { done. }
  move => ?. rewrite list_lookup_fmap => -[/fmap_Some[?[/reverse_lookup_Some[??] ?]] Hl].
  unfold byte in *; rewrite fmap_length in Hbs; simplify_eq.
  move: Hl => /reverse_lookup_Some [/bv_to_bits_lookup_Some[??] ?]; simplify_eq.
  by rewrite bool_of_bitU_of_bool bv_to_bits_length.
Qed.

Lemma read_mem_bytes_eq (len' : N) n bs:
  n = (length bs * 8) →
  len' = N.of_nat (length bs) →
     of_bits (n:=n) (bits_of_mem_bytes (byte_to_memory_byte <$> bs)) = Some
     (bv_to_mword (Z_to_bv (8 * len') (little_endian_to_bv 8 bs))).
Proof.
  move => ??.
  have n_pos : n >=? 0 = true by lia.
  rewrite /of_bits just_list_bits_of_mem_bytes n_pos /=. f_equal.
  apply get_word_inj. rewrite !get_word_to_word fit_bbv_word_id. {
    rewrite join_length -list_fmap_compose /compose /= (sum_list_fmap_same 8) ?reverse_length; [lia|].
    by apply Forall_true.
  }
  move => Hhyp. destruct Hhyp => /=. apply Word.wordToN_inj.
  rewrite Word.wordToN_NToWord_2. 2: {
    rewrite -Npow2_pow Z_to_bv_unsigned join_length -list_fmap_compose /compose /= (sum_list_fmap_same 8) ?reverse_length; [|by apply Forall_true].
    have ? := bv_wrap_in_range (8 * len') (little_endian_to_bv 8 bs).
    unfold bv_modulus in *.
    apply N2Z.inj_lt.
    have ->: N.of_nat (length bs * 8) = (8 * len')%N by lia.
    rewrite N2Z.inj_pow. lia.
  }
  apply N2Z.inj. rewrite Z2N.id. 2: {
    have ? := bv_unsigned_in_range _ (Z_to_bv (8 * len') (little_endian_to_bv 8 bs)). lia.
  }
  rewrite Z_to_bv_unsigned. apply Z.bits_inj_iff' => i ?.
  have {1}->: i = Z.of_nat (Z.to_nat i) by lia.
  rewrite wordFromBitlist_spec rev_reverse.
  rewrite bv_wrap_spec //. case_bool_decide => /=.
  2: { rewrite lookup_ge_None_2 // reverse_length join_length -list_fmap_compose /compose /= (sum_list_fmap_same 8) ?reverse_length; [lia|]. by apply Forall_true. }
  rewrite /default. case_match as Hc.
  2: { rewrite lookup_ge_None reverse_length join_length -list_fmap_compose /compose /= (sum_list_fmap_same 8) ?reverse_length in Hc; [lia|]. by apply Forall_true. }
  move: Hc => /reverse_lookup_Some [/(join_lookup_Some_same_length 8)[|j1 [?[j2[Hl[Hl2 Hi]]]] ?]]. {
    apply Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    by rewrite reverse_length bv_to_bits_length.
  }
  move: Hi => /Nat2Z.inj_iff. rewrite join_length -list_fmap_compose /compose /= (sum_list_fmap_same 8) ?reverse_length.
  2: { by apply Forall_forall. }
  move => Hi.
  have {Hi} ?: i = (length bs * 8 - 1 - (j1 * 8 + j2))%nat by lia. simplify_eq.
  move: Hl. rewrite list_lookup_fmap => /fmap_Some[?[/reverse_lookup_Some[Hbs ?] ?]]. simplify_eq.
  move: Hl2  => /reverse_lookup_Some[/bv_to_bits_lookup_Some[??]?]. simplify_eq/=.
  erewrite little_endian_to_bv_spec; [|lia|done|]. 2: { erewrite <-Hbs. f_equal. lia. }
  f_equal. lia.
Qed.

Definition register_value_to_valu (v : register_value) : valu :=
  match v with
  | Regval_bitvector_64_dec m => RVal_Bits (mword_to_bv (n2:=64) m)
  | Regval_bool b => RVal_Bool b
  | Regval_Misa m => RegVal_Struct [("bits", RVal_Bits (mword_to_bv (n2:=64) m.(Misa_bits)))]
  | Regval_Mstatus m => RegVal_Struct [("bits", RVal_Bits (mword_to_bv (n2:=64) m.(Mstatus_bits)))]
  | Regval_Privilege p => RVal_Enum (Mk_enum_id 3, Mk_enum_ctor (match p with | User => 0 | Supervisor => 1 | Machine => 2 end))
  | _ => RegVal_Poison
  end.

Lemma iris_module_wf_isla_lang :
  iris_module_wf isla_lang.
Proof. move => ?????? Hstep. inv_seq_step; split => //; try destruct κ' => /=; lia. Qed.

(*** operational semantics for [monad] *)
Inductive encoded_instruction :=
| Uncompressed (i : bv 32) | Compressed (i : bv 16).

Record sail_state := SAIL {
  sail_monad : M ();
  sail_regs : regstate;
  sail_mem : mem_map;
  sail_instrs : gmap addr encoded_instruction;
  sail_stopped : bool;
}.

Definition instruction_length (i : encoded_instruction) : mword 64 :=
  match i with
   | Uncompressed ie => mword_of_int 4
   | Compressed ie => mword_of_int 2
   end.

Definition step_cpu (i : encoded_instruction) : M () :=
  (match i with
   | Uncompressed ie => riscv.decode (bv_to_mword ie)
   | Compressed ie => riscv.decodeCompressed (bv_to_mword ie)
   end) >>= λ dec,
   read_reg PC_ref >>= λ PC,
   write_reg nextPC_ref (add_vec PC (instruction_length i)) >>
   execute dec >>= λ R, if R is RETIRE_SUCCESS then
                          read_reg nextPC_ref >>= λ nextPC,
                          write_reg PC_ref nextPC >>
                          Done tt
                        else
                          Fail "execution failed!".


Inductive sail_step : sail_state → option seq_label → sail_state → Prop :=
| SailDone rs h i ins :
  ins !! mword_to_bv (PC rs) = Some i →
  sail_step (SAIL (Done tt) rs h ins false) None (SAIL (step_cpu i) rs h ins false)
| SailStop rs h ins :
  ins !! mword_to_bv (PC rs) = None →
  sail_step (SAIL (Done tt) rs h ins false) (Some (SInstrTrap (mword_to_bv (PC rs)))) (SAIL (Done tt) rs h ins true)
| SailChoose rs h ins ty e s v:
  sail_step (SAIL (Choose s ty e) rs h ins false) None (SAIL (e v) rs h ins false)
| SailReadReg rs h ins e r v:
  get_regval r rs = Some v →
  sail_step (SAIL (Read_reg r e) rs h ins false) None (SAIL (e v) rs h ins false)
| SailWriteReg rs rs' h ins e r v:
  set_regval r v rs = Some rs' →
  sail_step (SAIL (Write_reg r v e) rs h ins false) None (SAIL e rs' h ins false)
| SailReadMem rs h ins e a bs' sz κ adr len:
  adr = (Z_to_bv 64 (Z.of_N a)) →
  (len = N.of_nat sz)%N →
  length bs' = sz →
  (if read_mem_list h (Z.of_N a) len is Some bs then
    κ = None ∧
    bs = bs'
  else
    Z.of_N a + Z.of_N len ≤ 2 ^ 64 ∧
    set_Forall (λ ad, ¬ (Z.of_N a ≤ bv_unsigned ad < Z.of_N a + Z.of_N len)) (dom h) ∧
    κ = Some (SReadMem adr (Z_to_bv (8 * len) (little_endian_to_bv 8 bs')))) →
  sail_step (SAIL (Read_mem Read_plain a sz e) rs h ins false) κ (SAIL (e (byte_to_memory_byte <$> bs')) rs h ins false)
| SailWriteMem rs h h' ins e a bs bs' sz len adr κ:
  adr = (Z_to_bv 64 (Z.of_N a)) →
  (len = N.of_nat sz)%N →
  bs = byte_to_memory_byte <$> bs' →
  (if read_mem_list h (Z.of_N a) len is Some _ then
    write_mem_list h (Z_to_bv 64 (Z.of_N a)) bs' = h' ∧
    κ = None
  else
    Z.of_N a + Z.of_N len ≤ 2 ^ 64 ∧
    set_Forall (λ ad, ¬ (Z.of_N a ≤ bv_unsigned ad < Z.of_N a + Z.of_N len)) (dom h) ∧
    h = h' ∧
    κ = Some (SWriteMem adr (Z_to_bv (8 * len) (little_endian_to_bv 8 bs')))) →
  sail_step (SAIL (Write_mem Write_plain a sz bs e) rs h ins false) κ (SAIL (e true) rs h' ins false)
| SailWriteEa rs h ins e wk n1 n2:
  sail_step (SAIL (Write_ea wk n1 n2 e) rs h ins false) None (SAIL e rs h ins false)
.

Definition sail_module := {|
  m_step := sail_step;
  m_non_ub_state σ := σ.(sail_stopped) ∨ ∃ κ σ', sail_step σ κ σ';
|}.

(*** [mctx]: Evaluation contexts for [monad] *)
Inductive mctx : Type → Type → Type :=
| NilMCtx : mctx () exception
| BindMCtx {A1 A2 E} (f : A1 → monad register_value A2 E) (K : mctx A2 E) : mctx A1 E
| TryMCtx {A E1 E2} (f : E1 → monad register_value A E2) (K : mctx A E2) : mctx A E1.

Fixpoint mctx_interp {A E} (K : mctx A E) : monad register_value A E → M () :=
  match K in (mctx A' E') return (monad register_value A' E' → M _) with
   | NilMCtx => λ e, e
   | BindMCtx f K => λ e, mctx_interp K (e >>= f)
   | TryMCtx f K => λ e, mctx_interp K (try_catch e f)
   end.

Lemma mctx_interp_Choose A E K s choose_ty e1:
  @mctx_interp A E K (Choose s choose_ty e1) = Choose s choose_ty (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Read_reg A E K r e1:
  @mctx_interp A E K (Read_reg r e1) = Read_reg r (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_reg A E K r e1 v:
  @mctx_interp A E K (Write_reg r v e1) = Write_reg r v (mctx_interp K e1).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Read_mem A E K e1 a sz rk:
  @mctx_interp A E K (Read_mem rk a sz e1) = Read_mem rk a sz (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_mem A E K e1 a sz bs wk:
  @mctx_interp A E K (Write_mem wk a sz bs e1) = Write_mem wk a sz bs (λ v, mctx_interp K (e1 v)).
Proof. elim: K e1 => //=. Qed.
Lemma mctx_interp_Write_ea A E K n1 n2 wk e1:
  @mctx_interp A E K (Write_ea wk n1 n2 e1) = Write_ea wk n1 n2 (mctx_interp K e1).
Proof. elim: K e1 => //=. Qed.

(*** [sim]: Simulation relation *)
Definition get_plat_config (reg_name : string) : option register_value :=
  match reg_name with
  | "rv_enable_pmp" => Some (Regval_bool (plat_enable_pmp ()))
  | "rv_enable_misaligned_access" => Some (Regval_bool (plat_enable_misaligned_access ()))
  | "rv_ram_base" => Some (Regval_bitvector_64_dec (plat_ram_base ()))
  | "rv_ram_size" => Some (Regval_bitvector_64_dec (plat_ram_size ()))
  | "rv_rom_base" => Some (Regval_bitvector_64_dec (plat_rom_base ()))
  | "rv_rom_size" => Some (Regval_bitvector_64_dec (plat_rom_size ()))
  | "rv_clint_base" => Some (Regval_bitvector_64_dec (plat_clint_base ()))
  | "rv_clint_size" => Some (Regval_bitvector_64_dec (plat_clint_size ()))
  | "rv_htif_tohost" => Some (Regval_bitvector_64_dec (plat_htif_tohost ()))
  | "Machine" => Some (Regval_Privilege (Machine))
  | _ => None
  end.

Definition get_regval_or_config (reg_name : string) (s : regstate) : option register_value :=
  match get_regval reg_name s with
  | Some v => Some v
  | None => get_plat_config reg_name
  end.

Definition isla_regs_wf (regs : regstate) (isla_regs : reg_map) : Prop :=
  ∀ r vi, isla_regs !! r = Some vi → ∃ vs, get_regval_or_config r regs = Some vs ∧ vi = (register_value_to_valu vs).

Definition private_regs_wf (isla_regs : reg_map) : Prop :=
  isla_regs !! "nextPC" = None.

Record sim_state := SIM {
  sim_regs : regstate;
}.
Add Printing Constructor sim_state.
Global Instance eta_sim_state : Settable _ := settable! SIM <sim_regs>.

Definition sim {A E} (Σ : sim_state) (e1 : monad register_value A E) (K : mctx A E) (e2 : isla_trace) : Prop :=
  ∀ n isla_regs mem sail_instrs isla_instrs,
  isla_regs_wf Σ.(sim_regs) isla_regs →
  private_regs_wf isla_regs →
  (∀ sail_regs' isla_regs' mem',
      isla_regs_wf sail_regs' isla_regs' →
      private_regs_wf isla_regs' →
      dom isla_regs' = dom isla_regs →
      raw_sim sail_module (iris_module isla_lang) n
          (SAIL (Done tt) sail_regs' mem' sail_instrs false)
          ({| seq_trace := tnil; seq_regs := isla_regs'; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem' |})) →
  raw_sim sail_module (iris_module isla_lang) n
          (SAIL (mctx_interp K e1) Σ.(sim_regs) mem sail_instrs false)
          ({| seq_trace := e2; seq_regs := isla_regs; seq_nb_state := false; seq_pc_reg := arch_pc_reg|},
           {| seq_instrs := isla_instrs; seq_mem := mem |}).

Definition sim_instr (si : encoded_instruction) (i : isla_trace) :=
  ∀ regs, sim (SIM regs) (step_cpu si) NilMCtx i.

Lemma sim_implies_refines sail_instrs isla_instrs sail_regs isla_regs mem :
  dom isla_instrs = dom sail_instrs →
  isla_regs_wf sail_regs isla_regs →
  private_regs_wf isla_regs →
  (∀ a si ii, sail_instrs !! a = Some si → isla_instrs !! a = Some ii → sim_instr si ii) →
  refines sail_module (SAIL (Done tt) sail_regs mem sail_instrs false)
          (iris_module isla_lang) (initial_local_state isla_regs, {| seq_instrs := isla_instrs; seq_mem := mem |}).
Proof.
  move => Hdom Hregs Hpriv Hsim. apply: raw_sim_implies_refines => n.
  elim/lt_wf_ind: n sail_regs isla_regs mem Hregs Hpriv.
  move => n IH sail_regs isla_regs mem Hregs Hpriv.
  apply: raw_sim_safe_here => /= Hsafe.
  have {Hsafe} ? : isla_regs !! "PC" = Some (RVal_Bits (mword_to_bv (n2:=64) (PC sail_regs))). {
    destruct (isla_regs !! "PC") eqn: HPC.
    - have [? [[<-] ->]]:= Hregs "PC" _ ltac:(done). done.
    - move: Hsafe => [[]|]// [?[?[?[? Hsafe]]]]. inv_seq_step.
      revert select (∃ x, _) => -[?[??]]; unfold register_name in *; simplify_eq.
  }
  destruct (sail_instrs !! mword_to_bv (PC sail_regs)) as [si|] eqn: Hsi.
  - move: (Hsi) => /(elem_of_dom_2 _ _ _). rewrite -Hdom. move => /elem_of_dom[ii Hii]. clear Hdom.
    have {}Hsim:= Hsim _ _ _ ltac:(done) ltac:(done) sail_regs.
    apply: raw_sim_step_i. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
    apply: raw_sim_step_s. {
      econstructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: Hsim; [done..|].
    move => sail_regs' isla_regs' mem' Hwf' ??.
    apply IH; [lia|done..].
  - move: (Hsi) => /(not_elem_of_dom). rewrite -Hdom. move => /not_elem_of_dom Hii. clear Hdom.
    constructor => Hsafe. split. { right. eexists _, _. by econstructor. }
    move => ???? Hstep. inversion_clear Hstep; simplify_eq. eexists _. split. {
      apply: (steps_l _ _ _ _ (Some _)); [| by apply: steps_refl].
      constructor. econstructor; [done| econstructor |] => /=. split; [done|].
      eexists _; simplify_option_eq. naive_solver.
    }
    apply: raw_sim_step_i. { by left. }
    move => ???? Hstep. inversion Hstep.
    Unshelve. exact: inhabitant.
Qed.

(*** Lemmas about [sim] *)
Lemma get_plat_config_Some_get_regval r regs x:
  get_plat_config r = Some x →
  get_regval r regs = None.
Proof. unfold get_plat_config. repeat case_match => //. Qed.

Lemma get_set_regval_config_ne r r' regs regs' v:
  set_regval r' v regs = Some regs' →
  r ≠ r' →
  get_regval_or_config r regs' = get_regval_or_config r regs.
Proof.
  move => Hset Hr. rewrite /get_regval_or_config.
  case_match as Hreg.
  - erewrite <-get_set_regval_ne; [|done..]. by rewrite Hreg.
  - by erewrite get_regval_None_stable.
Qed.

Lemma sim_done Σ:
  sim Σ (Done tt) NilMCtx tnil.
Proof. move => ??????? Hdone. by apply: Hdone. Qed.

Lemma sim_mctx_impl A1 A2 E1 E2 Σ e11 e12 K1 K2 e2:
  sim (A:=A1) (E:=E1) Σ e11 K1 e2 →
  mctx_interp K1 e11 = mctx_interp K2 e12 →
  sim (A:=A2) (E:=E2) Σ e12 K2 e2.
Proof. rewrite /sim => ? <-. done. Qed.

Lemma sim_bind A1 A2 E Σ e1 f K e2:
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2 →
  sim (A:=A2) (E:=E) Σ (e1 >>= f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.
Lemma sim_try_catch A E1 E2 Σ e1 f K e2:
  sim (A:=A) (E:=E2) Σ e1 (TryMCtx f K) e2 →
  sim (A:=A) (E:=E1) Σ (try_catch e1 f) K e2.
Proof. move => ?. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind A1 A2 E Σ K e1 f e2:
  sim (A:=A2) Σ (e1 >>= f) K e2 →
  sim (A:=A1) (E:=E) Σ e1 (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_catch A E1 E2 Σ K e1 f e2:
  sim (A:=A) (E:=E2) Σ (try_catch e1 f) K e2 →
  sim (A:=A) (E:=E1) Σ e1 (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_pop_bind_Done A1 A2 E Σ K v f e2:
  sim (A:=A2) Σ (f v) K e2 →
  sim (A:=A1) (E:=E) Σ (Done v) (BindMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.
Lemma sim_pop_try_Done A E1 E2 Σ K v f e2:
  sim (A:=A) (E:=E2) Σ (Done v) K e2 →
  sim (A:=A) (E:=E1) Σ (Done v) (TryMCtx f K) e2.
Proof. move => Hsim. by apply: sim_mctx_impl. Qed.

Lemma sim_Choose {A E} Σ s ty e1 e2 K:
  (∀ v, sim Σ (e1 v) K e2) →
  sim (A:=A) (E:=E) Σ (Choose s ty e1) K e2.
Proof.
  move => Hsim ????????/=. rewrite mctx_interp_Choose.
  apply: raw_sim_step_i. { right. eexists _, _. unshelve constructor. by apply: Values.inhabitant. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_Read_reg_l {A E} Σ r e1 e2 v K:
  get_regval r Σ.(sim_regs) = Some v →
  sim Σ (e1 v) K e2 →
  sim (A:=A) (E:=E) Σ (Read_reg r e1) K e2.
Proof.
  move => ? Hsim ????????. rewrite mctx_interp_Read_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_read_reg_l A E Σ (r : register_ref regstate register_value A) K e2:
  (v' ← get_regval (name r) Σ.(sim_regs); of_regval r v') = Some (read_from r Σ.(sim_regs)) →
  sim Σ (Done (read_from r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K e2.
Proof.
  move => /bind_Some[rv [? Hof]] Hsim.
  apply: sim_Read_reg_l; [done|] => ??. rewrite Hof.
  by apply: Hsim.
Qed.

Lemma sim_read_reg A E Σ K e2 ann r v v':
  get_regval (name r) Σ.(sim_regs) = Some v' →
  of_regval r v' = Some (read_from r Σ.(sim_regs)) →
  v = register_value_to_valu v' →
  sim (A:=A) (E:=E) Σ (Done (read_from r Σ.(sim_regs))) K e2 →
  sim (A:=A) (E:=E) Σ (read_reg r) K (ReadReg (name r) [] v ann :t: e2).
Proof.
  move => Hget Hof -> Hsim. apply: sim_read_reg_l; [ by simplify_option_eq|].
  move => ? isla_regs ??? Hwf??.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (name r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor => //=. 1: by econstructor.
    simpl. have [?[??]]:= Hwf (name r) _ ltac:(done).
    unfold get_regval_or_config in *. simplify_option_eq.
    eexists _, _, _. split_and! => //. by left. }
  by apply: Hsim.
Qed.

Lemma sim_ReadReg_config A E Σ K e1 e2 ann r v v':
  get_plat_config r = Some v' →
  v = register_value_to_valu v' →
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (ReadReg r [] v ann :t: e2).
Proof.
  move => Hget -> Hsim ? isla_regs ??? Hwf??.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! r). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor => //=. 1: by econstructor.
    simpl. have [?[Hr ?]]:= Hwf r _ ltac:(done). unfold get_regval_or_config in *.
    erewrite get_plat_config_Some_get_regval in Hr; [|done]. simplify_option_eq.
    eexists _, _, _. split_and! => //. by left. }
  by apply: Hsim.
Qed.

Lemma sim_write_reg {A E} Σ (r : register_ref _ _ A) e2 v K v' ann:
  name r ≠ "tlb48" ∧ name r ≠ "tlb39" →
  set_regval (name r) (regval_of r v) Σ.(sim_regs) = Some (write_to r v Σ.(sim_regs)) →
  v' = register_value_to_valu (regval_of r v) →
  sim (Σ <|sim_regs := write_to r v Σ.(sim_regs)|>) (Done tt) K e2 →
  sim (E:=E) Σ (write_reg r v) K (WriteReg (name r) [] v' ann :t: e2).
Proof.
  destruct Σ => /=.
  move => ? Hset -> Hsim ? isla_regs ? ?? Hwf ? Hdone. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have [vi Hvi]: is_Some (isla_regs !! (name r)). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step. naive_solver.
  }
  apply: raw_sim_step_s. {
    econstructor. econstructor; [done| by econstructor|] => /=.
    eexists _, _, _. done.
  }
  apply: raw_sim_weaken; [apply Hsim => /=| ].
  - move => r' vi'. destruct (decide (r' = name r)); simplify_eq.
    + rewrite lookup_insert. move: Hset => /get_set_regval.
      unfold get_regval_or_config => ->; naive_solver.
    + rewrite lookup_insert_ne //.
      erewrite get_set_regval_config_ne; [|done..]. by apply: Hwf.
  - apply/lookup_insert_None. unfold private_regs_wf in *.
    split; [done|]. move => Hn. rewrite Hn in Hvi. naive_solver.
  - move => ????? Hdom. apply: Hdone; [done..|]. by rewrite Hdom dom_insert_lookup_L.
  - lia.
Qed.

Lemma sim_write_reg_private {A E} Σ (r : register_ref _ _ A) e2 v K:
  set_regval (name r) (regval_of r v) Σ.(sim_regs) = Some (write_to r v Σ.(sim_regs)) →
  name r = "nextPC" →
  sim (Σ <|sim_regs := write_to r v Σ.(sim_regs)|>) (Done tt) K e2 →
  sim (E:=E) Σ (write_reg r v) K e2.
Proof.
  destruct Σ => /=.
  move => Hset Heq Hsim ? isla_regs ? ?? Hwf ? Hdone. rewrite mctx_interp_Write_reg.
  apply: raw_sim_step_i. { right. eexists _, _. by constructor. }
  move => ????/= Hstep. inversion_clear Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [apply Hsim => /=; [|done..]| lia].
  move => ?? Hisla. have [?[??]]:= Hwf _ _ ltac:(done).
  eexists _. split; [|done].
  erewrite get_set_regval_config_ne; [done..|].
  move => ?. subst. unfold private_regs_wf in *. rewrite Heq in Hisla. naive_solver.
Qed.

Lemma sim_Write_ea {A E} Σ e1 e2 K n2 n1 wk:
  sim Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ (Write_ea wk n1 n2 e1) K e2.
Proof.
  move => Hsim ????????/=. rewrite mctx_interp_Write_ea.
  apply: raw_sim_step_i. { right. eexists _, _. constructor. }
  move => ????/= Hstep. inversion Hstep; simplify_eq. split; [done|].
  apply: raw_sim_weaken; [by apply: Hsim| lia].
Qed.

Lemma sim_write_mem {E} Σ e2 n' (sz : Z) (v : mword (8 * sz)) K (v' : bv n') ann res wk' (a : mword 64) (a' : addr) len' d:
  (8 * len' = n')%N →
  sz = Z.of_N len' →
  res = RVal_Bool true →
  mword_to_bv a = a' →
  mword_to_bv v = v' →
  sim Σ (Done true) K e2 →
  sim (E:=E) Σ (Prompt_monad.write_mem Write_plain d a sz v) K (WriteMem res wk' (RVal_Bits a') (RVal_Bits v') len' None ann :t: e2).
Proof.
  move => ? ? ? ? ? Hsim ? isla_regs mem ?? Hwf ? Hdone. subst.
  set a' := mword_to_bv a. set v' := mword_to_bv (n2:=8 * len') v.
  unfold Prompt_monad.write_mem. simplify_option_eq.
  erewrite mem_bytes_of_bits_to_bv; [|done|lia].
  rewrite mctx_interp_Write_mem.
  apply: raw_sim_safe_here => /= -[|Hsafe]. { unfold seq_to_val. by case. }
  have {Hsafe}[? Hor] : 0 < Z.of_N len' ∧ (is_Some (read_mem_list mem (bv_unsigned a') len') ∨
    (read_mem_list mem (bv_unsigned a') len' = None ∧
       bv_unsigned a' + Z.of_N len' ≤ 2 ^ 64 ∧
       set_Forall (λ ad, ¬ (bv_unsigned a' ≤ bv_unsigned ad < bv_unsigned a' + Z.of_N len')) (dom mem))). {
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step.
    revert select (∃ m, _) => -[?[?[?[Ha'[ _ [??]]]]]].
    injection Ha'. intros ?%Eqdep_dec.inj_pair2_eq_dec. 2: { by move => ??; apply decide; apply _. } subst.
    split; [done|]. case_match as Hmem.
    + move: Hmem => /fmap_Some. naive_solver.
    + move: Hmem => /fmap_None. naive_solver.
  }
  have Heq : Z.of_N (Word.wordToN a) = bv_unsigned a'.
  { rewrite mword_to_bv_unsigned //. }
  have Heq2 : (bv_unsigned (mword_to_bv (n2:=(Z.to_N (8 * Z.of_N len'))) v) = (bv_unsigned v')).
  { rewrite /v' !mword_to_bv_unsigned //; lia. }
  constructor => _. split. {
    right. move: Hor => [[? Hm]//|[Hm [??]]].
    all: eexists _, _; eapply SailWriteMem; [done..|].
    all: by rewrite !Z_nat_N !N2Z.id !Heq Z_to_bv_bv_unsigned Hm.
  }
  move => ? ? ? ? Hstep. inversion_clear Hstep; simplify_eq.
  move: H2. rewrite !Z_nat_N !N2Z.id !Heq Z_to_bv_bv_unsigned.
  move: Hor => [[? Hm]//|[Hm ?]]; rewrite Hm.
  - move => [??]. simplify_eq. eexists _. split. {
      apply: (steps_l' _ _ _ _ _ []); [ |by apply: steps_refl| by rewrite right_id_L].
      econstructor. econstructor; [done| by econstructor|] => /=.
      eexists _, _, v'. split_and! => //.
      by rewrite /read_mem Hm.
    }
    rewrite /write_mem N_nat_Z Heq2.
    apply: raw_sim_weaken; [by apply Hsim| lia].
  - move => [?[?[??]]]. simplify_eq. eexists _. split. {
      apply: (steps_l' _ _ _ _ _ []); [ |by apply: steps_refl| by rewrite right_id_L].
      econstructor. econstructor; [done| by econstructor|] => /=.
      eexists _, _, v'. split_and! => //.
      rewrite /read_mem Hm /=. split_and! => //.
      rewrite Heq2 Z_to_bv_little_endian_to_bv_to_little_endian //; lia.
    }
    apply: raw_sim_weaken; [by apply Hsim| lia].
    Unshelve. apply: inhabitant.
Qed.

Lemma sim_read_mem {E} Σ (sz : Z) e2 K ann ann' rk' (a : mword 64) (a' : addr) len' len'' d sm:
  len'' = (8 * len')%N →
  sz = Z.of_N len' →
  mword_to_bv a = a' →
  (∀ r1 (r2 : bv len''), r1 = bv_to_mword r2 → sim Σ (Done r1) K (subst_trace (Val_Bits r2) sm e2)) →
  sim (E:=E) Σ (Prompt_monad.read_mem Read_plain d a sz) K
      (Smt (DeclareConst sm (Ty_BitVec len'')) ann' :t:
       ReadMem (RVal_Symbolic sm) rk' (RVal_Bits a') len' None ann :t: e2).
Proof.
  move => ? ? ? Hsim. subst. set a' := mword_to_bv a.
  unfold Prompt_monad.read_mem, read_mem_bytes. apply sim_bind.
  move => ? isla_regs mem ?? Hwf ? Hdone. rewrite mctx_interp_Read_mem.
  have Heq : Z.of_N (Word.wordToN a) = bv_unsigned a'.
  { rewrite mword_to_bv_unsigned //. }
  constructor => Hsafe.
  have {Hsafe}[? Hor] : 0 < Z.of_N len' ∧ (is_Some (read_mem_list mem (bv_unsigned a') len') ∨
    (read_mem_list mem (bv_unsigned a') len' = None ∧
       bv_unsigned a' + Z.of_N len' ≤ 2 ^ 64 ∧
       set_Forall (λ ad, ¬ (bv_unsigned a' ≤ bv_unsigned ad < bv_unsigned a' + Z.of_N len')) (dom mem))). {
    efeed pose proof Hsafe as He.
    { apply: steps_l'; [|apply steps_refl|done].
      constructor. econstructor; [done|eapply (DeclareConstBitVecS' (bv_0 _))|] => /=. done. }
    move: He => [| {}Hsafe]. { unfold seq_to_val. by case. }
    move: Hsafe => [?[?[?[? Hstep]]]]. inv_seq_step.
    revert select (∃ m, _) => -[?[?[?[Ha'[ _ [??]]]]]].
    injection Ha'. intros ?%Eqdep_dec.inj_pair2_eq_dec. 2: { by move => ??; apply decide; apply _. } subst.
    split; [done|]. case_match as Hmem.
    + move: Hmem => /fmap_Some. naive_solver.
    + move: Hmem => /fmap_None. naive_solver.
  }
  split. {
    right. move: Hor => [[? Hm]//|[Hm [??]]].
    all: eexists _, _; eapply SailReadMem; [done..| | by rewrite !Z_nat_N !N2Z.id !Heq Z_to_bv_bv_unsigned Hm].
    - move: Hm => /mapM_Some /Forall2_length <-. rewrite seqZ_length. lia.
    - apply replicate_length.
  }
  move => ? ? ? ? Hstep. inversion_clear Hstep; simplify_eq.
  move: H2. rewrite !Z_nat_N !N2Z.id !Heq Z_to_bv_bv_unsigned.
  rewrite (read_mem_bytes_eq len') /=.
  2: { rewrite H1. lia. } 2: { rewrite H1. lia. }
  move: Hor => [[? Hm]//|[Hm ?]]; rewrite Hm.
  - move => [??]. simplify_eq. eexists _. split. {
      apply: steps_l'.
      { econstructor. econstructor; [done| eapply DeclareConstBitVecS' |] => /=. done. } 2: done.
      apply: (steps_l' _ _ _ _ None); [ |by apply: steps_refl| by rewrite right_id_L ].
      econstructor. econstructor; [done| by econstructor|]; csimpl.
      eexists _, _, _. split_and! => //. { by rewrite /eq_var_name Z.eqb_refl. }
      rewrite /read_mem Hm/=. split_and! => //. by left.
    }
    apply: raw_sim_weaken; [by apply Hsim|lia].
  - move => [?[??]]. simplify_eq. eexists _. split. {
      apply: steps_l'.
      { econstructor. econstructor; [done| apply: DeclareConstBitVecS'; shelve|] => /=. done. } 2: done.
      apply: (steps_l' _ _ _ _ (Some _)); [ |by apply: steps_refl| by rewrite right_id_L ].
      econstructor. econstructor; [done| by econstructor|]; csimpl.
      eexists _, _, _. split_and! => //. { by rewrite /eq_var_name Z.eqb_refl. }
      by rewrite /read_mem Hm/=.
    }
    apply: raw_sim_weaken; [by apply Hsim| lia].
    Unshelve. all: apply inhabitant.
Qed.

Lemma sim_assert_exp' E Σ b K e2 s:
  b = true →
  (∀ H, sim Σ (Done H) K e2) →
  sim (E:=E) Σ (assert_exp' b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp'. destruct b => //. Qed.

Lemma sim_assert_exp E Σ b K e2 s:
  b = true →
  sim Σ (Done tt) K e2 →
  sim (E:=E) Σ (assert_exp b s) K e2.
Proof. move => Hb Hsim. unfold assert_exp. destruct b => //. Qed.

Lemma sim_tcases i A E Σ K e1 ts t:
  ts !! i = Some t →
  sim (A:=A) (E:=E) Σ e1 K t →
  sim (A:=A) (E:=E) Σ e1 K (tcases ts).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor; eapply elem_of_list_lookup_2. done.  }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstBool A E Σ K e1 e2 ann x b:
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Bool b) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x Ty_Bool) ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstBitVec A E Σ K e1 e2 ann x b (v : bv b):
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Bits v) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x (Ty_BitVec b)) ann :t: e2).
Proof.
  move => Hsim ????????. destruct v.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DeclareConstEnum A E Σ K e1 e2 ann x id c:
  sim (A:=A) (E:=E) Σ e1 K (subst_trace (Val_Enum (id, c)) x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DeclareConst x (Ty_Enum id)) ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_DefineConst A E Σ K e1 e2 ann x v e:
  eval_exp e = Some v →
  sim (A:=A) (E:=E) Σ e1 K (subst_trace v x e2) →
  sim (A:=A) (E:=E) Σ e1 K (Smt (DefineConst x e) ann :t: e2).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_Branch A E Σ K e1 e2 ann n s:
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (Branch n s ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_BranchAddress A E Σ K e1 e2 ann v:
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (BranchAddress v ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Lemma sim_Assert A E Σ K e1 e2 ann e:
  eval_exp e = Some (Val_Bool true) →
  sim (A:=A) (E:=E) Σ e1 K e2 →
  sim (A:=A) (E:=E) Σ e1 K (Smt (Assert e) ann :t: e2).
Proof.
  move => ? Hsim ????????.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  by apply: Hsim.
Qed.

Definition eval_assume_val' (regs : regstate) (v : assume_val) : option base_val :=
  match v with
  | AVal_Var r l => v' ← get_regval_or_config r regs;
                   v'' ← read_accessor l (register_value_to_valu v');
                   if v'' is RegVal_Base b then Some b else None
  | AVal_Bool b => Some (Val_Bool b)
  | AVal_Bits b => Some (Val_Bits b)
  | AVal_Enum e => Some (Val_Enum e)
  end.

Fixpoint eval_a_exp' (regs : regstate) (e : a_exp) : option base_val :=
  match e with
  | AExp_Val x _ => eval_assume_val' regs x
  | AExp_Unop uo e' _ =>
    eval_a_exp' regs e' ≫= eval_unop uo
  | AExp_Binop uo e1 e2 _ =>
    v1 ← eval_a_exp' regs e1; v2 ← eval_a_exp' regs e2; eval_binop uo v1 v2
  | AExp_Manyop m es _ => vs ← mapM (eval_a_exp' regs) es; eval_manyop m vs
  | AExp_Ite e1 e2 e3 _ =>
    match eval_a_exp' regs e1 with
    | Some (Val_Bool true) => eval_a_exp' regs e2
    | Some (Val_Bool false) => eval_a_exp' regs e3
    | _ => None
    end
  end.

Lemma eval_assume_val'_sound isla_regs sail_regs e v:
  eval_assume_val isla_regs e = Some v →
  isla_regs_wf sail_regs isla_regs →
  eval_assume_val' sail_regs e = Some v.
Proof.
  destruct e => //=.
  move => /bind_Some[?[? ?]] Hwf.
  have [?[-> ?]]:= Hwf _ _ ltac:(done). by subst.
Qed.

Lemma eval_a_exp'_sound isla_regs sail_regs e v:
  eval_a_exp isla_regs e = Some v →
  isla_regs_wf sail_regs isla_regs →
  eval_a_exp' sail_regs e = Some v.
Proof.
  (* TODO: use a proper induction principled instead of a_exp_ott_ind such that it can be used with induction *)
  revert e v. match goal with | |- ∀ e, @?P e => eapply (a_exp_ott_ind (λ es, Forall P es) P) end => /=.
  - move => ????. by apply: eval_assume_val'_sound.
  - move => ?? IH ?? /bind_Some[?[/IH He ?]] ?. by rewrite He.
  - move => ?? IH1 ? IH2 ?? /bind_Some[?[/IH1 He1 /bind_Some[?[/IH2 He2 ?]]]] ?. by rewrite He1 ?He2.
  - move => es /Forall_lookup IHes ??? /bind_Some[?[/mapM_Some /Forall2_same_length_lookup [? Hes] ?]] ?.
    apply/bind_Some. eexists _. split; [|done]. apply/mapM_Some. apply/Forall2_same_length_lookup.
    naive_solver.
  - move => e1 IH1 e2 IH2 e3 IH3 ??.
    destruct (eval_a_exp isla_regs e1) eqn: He1 => // Hb ?.
    have -> := IH1 _ ltac:(done) ltac:(done).
    destruct b as [| [] | |] => //; naive_solver.
  - constructor.
  - move => ????. by constructor.
Qed.

Lemma sim_Assume A E Σ K e1 e2 ann e:
  (eval_a_exp' Σ.(sim_regs) e = Some (Val_Bool true) → sim (A:=A) (E:=E) Σ e1 K e2) →
  sim (A:=A) (E:=E) Σ e1 K (Assume e ann :t: e2).
Proof.
  move => Hsim ????????.
  apply: raw_sim_safe_here => -[[??//]|[?[?[?[??]]]]]. inv_seq_step.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. done. }
  apply: Hsim; [|done..].
  by apply: eval_a_exp'_sound.
Qed.

Lemma sim_AssumeReg A E Σ K e1 e2 ann r v al:
  ((v' ← get_regval_or_config r Σ.(sim_regs); read_accessor al (register_value_to_valu v')) = Some v
    → sim (A:=A) (E:=E) Σ e1 K e2) →
  sim (A:=A) (E:=E) Σ e1 K (AssumeReg r al v ann :t: e2).
Proof.
  move => Hsim ????? Hwf ??.
  apply: raw_sim_safe_here => -[[??//]|[?[?[?[??]]]]]. inv_seq_step.
  revert select (∃ v, _) => -[?[?[?[?[??]]]]]. simplify_eq.
  apply: raw_sim_step_s. { econstructor. econstructor => //=. 1: by econstructor. naive_solver. }
  apply: Hsim; [|done..].
  have [?[??]]:= Hwf r _ ltac:(done). simplify_eq.
  apply/bind_Some. naive_solver.
Qed.
