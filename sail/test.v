Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sail.Base.
Require Import Sail.State_monad.
Require Import Sail.State_lifting.
Require Import isla.sail.sail_opsem.
Require Import isla.sys_regs.
From isla.instructions.example Require Import instrs.

(*
Definition _admit {T} : T.
Admitted.

Program Definition initial_state : regstate :=
  {| SEE := 0 |}.
Solve Obligations with try exact: _admit.
Definition init_state : sequential_state regstate := {|
                         ss_regstate := initial_state ;
                         ss_memstate := NatMap.empty _;
                         ss_tagstate := NatMap.empty _;
                       |}.
Eval hnf in (liftState register_accessors (decode64 (Pos.to_nat 32 'h "AA0303F3" : mword 32)) init_state).
 *)

Definition test_regs :=
    <[ "_PC" := RVal_Bits ([BV{64} 0x0000000010300000 - 4]) ]> $
    <[ "__PC_changed" := RVal_Bool false ]> $
    <[ "R30" := RegVal_Poison ]> $
    <[ "R1" := RegVal_Poison ]> $
    <[ "R0" := RegVal_Poison ]> $
    <[ "R27" := RVal_Bits [BV{64} 0x101f1000] ]> $
    <[ "R28" := RegVal_Poison ]> $
    <[ "PSTATE" := (RegVal_Struct
    [("C", RVal_Bits [BV{1} 0]);
    ("SP", RVal_Bits [BV{1} 1]); ("N", RVal_Bits [BV{1} 0]);
    ("D", RVal_Bits [BV{1} 1]);
    ("nRW", RVal_Bits [BV{1} 0]); ("EL", RVal_Bits [BV{2} 2]);
    ("Z", RVal_Bits [BV{1} 0]); ("BTYPE", RegVal_Poison);
    ("V", RVal_Bits [BV{1} 0])]) ]> $
     sys_regs_map
.

Definition test_mapped_regs : gset string :=
    {[ "_PC"; "__PC_changed"; "PSTATE" ]}
.

Definition test_instrs : gmap addr (bv 32 * list trc) :=
    <[ [BV{64} 0x0000000010300000] := ([BV{32} 0x94000004], a0)]> $
    <[ [BV{64} 0x0000000010300004] := ([BV{32} 0xaa0003fc], a4)]> $
    <[ [BV{64} 0x0000000010300008] := ([BV{32} 0xf900037c], a8)]> $

    <[ [BV{64} 0x0000000010300010] := ([BV{32} 0x52800000], a10)]> $
    <[ [BV{64} 0x0000000010300014] := ([BV{32} 0xd65f03c0], a14)]> $
    ∅.


(* Ltac arch_red := lazy [ *)
(*                       write_reg read_reg *)
(*                       bind0 name __unconditional_ref PSTATE_ref of_regval regval_of regval_of_bool *)
(*                       undefined_SRType internal_pick *)
(*                       returnm eq_vec Bool.eqb get_word Word.whd *)
(*                       Word.natToWord bin readBinNat readBinAux forceOption *)
(*                       Pos.to_nat Pos.iter_op Init.Nat.add Init.Nat.mul Nat.div2 binDigitToNat *)
(*                       NatLib.mod2 Word.wtl *)
(*                       uint projT1 uint_plain Word.wordToN *)
(*                       N.mul Z.of_N Z.eqb orb andb sumbool_of_bool *)
(*                       and_boolM HaveBTIExt HasArchVersion generic_eq *)
(*                       Decidable_witness Decidable_eq_ArchVersion *)
(*                       Decidable_eq_from_dec bool_of_sumbool ArchVersion_eq_dec *)
(*                       ArchVersion_beq sumbool_rec sumbool_rect proj1_sig *)
(*                       __v85_implemented UsingAArch32 *)
(*                       HaveAnyAArch32 Z.to_nat *)
(*                       CFG_ID_AA64PFR0_EL1_EL1  CFG_ID_AA64PFR0_EL1_EL0 *)
(*                       HighestELUsingAArch32 __highest_el_aarch32_ref SEE_ref *)
(*                       Word.NToWord hex readHexN readHexNAux hexDigitToN *)
(*                       Word.wzero' Word.posToWord N.add negb *)
(*                       Pos.mul Pos.add Pos.pred_double *)
(*                       N.succ Pos.succ *)
(*                       undefined_bool *)
(*                       choose_bool *)
(*                       undefined_LogicalOp *)
(*                       aget_X *)
(*                       neq_int *)
(*                       _R_ref *)
(*                       build_ex *)
(*                       Pos.eqb *)
(*                       __id *)
(*                       (* access_vec_dec *) *)
(*                       (* access_mword_dec *) *)
(*                       (* bitU_of_bool getBit Word.wlsb Word.wrshift' *) *)
(*                       (* subrange_vec_dec *) *)
(*                       (* cast_to_mword cast_T mword_of_nat *) *)
(*                       (* cast_word Word.split1 Word.split2 *) *)
(*                     ]. *)
(*   Ltac do_red := *)
(*     repeat first [ *)
(*         progress arch_red | *)
(*         progress repeat match goal with *)
(*                         | |- context [@subrange_vec_dec ?n ?a ?b ?c ?F1 ?F2] => progress reduce_closed (@subrange_vec_dec n a b c F1 F2) *)
(*                         | |- context [@access_vec_dec ?n ?w ?m] => progress reduce_closed (@access_vec_dec n w m) *)
(*                         | |- context [vec_of_bits ?l] => progress reduce_closed (vec_of_bits l) *)
(*                         | |- context [Word.weqb ?b1 ?b2] => progress reduce_closed (Word.weqb b1 b2) *)
(*                         | |- context [Z.add ?n1 ?n2] => progress reduce_closed (Z.add n1 n2) *)
(*                         | |- context [Z.sub ?n1 ?n2] => progress reduce_closed (Z.sub n1 n2) *)
(*                         end | *)
(*         progress cbn [bind] *)
(*       ]. *)


(*
Axiom AXIOM_sim_TakePendingInterrupts : ∀ n Σ i e1 e2,
  sim n Σ e1 e e2 →
  sim n Σ
(undefined_InterruptReq () >>=
     (λ interrupt_req : InterruptReq,
        try_catch
          (TakePendingInterrupts (i interrupt_req) >>=
           (λ w__0 : bool,
              returnm
                (if sumbool_of_bool w__0
                 then print "Pending interrupt taken
"
                 else ())))
          (λ _ : exception,
             returnm (print "Unhandled exception while pending exceptions
")) >> e1)) e2.
 *)

(*** reduction tactics *)
Ltac hnf_sim :=
  match goal with
  | |- sim _ _ ?e1 _ _ =>
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
   | |- context [cast_unit_vec ?b] => progress reduce_closed (cast_unit_vec b)
   | |- context [@neq_vec ?n ?b1 ?b2] => progress reduce_closed (@neq_vec n b1 b2)
   | |- context [Z.ltb ?n1 ?n2] => progress reduce_closed (Z.ltb n1 n2)
   | |- context [neq_int ?n1 ?n2] => progress reduce_closed (neq_int n1 n2)
   | |- context [HaveAnyAArch32 ()] => progress reduce_closed (HaveAnyAArch32 ())
   | |- context [HaveNV2Ext ()] => progress reduce_closed (HaveNV2Ext ())
   | |- context [HaveBTIExt ()] => progress reduce_closed (HaveBTIExt ())
   end.

Ltac cbn_sim :=
  cbn [returnm bind bind0 sim_regs sim_mapped_regs sim_mem sim_instrs
       ProcState_of_regval of_regval read_from write_to
       PSTATE_ref _PC_ref HCR_EL2_ref SCTLR_EL1_ref SEE_ref __unconditional_ref _R_ref __currentInstr_ref
       negb sumbool_of_bool set
       projT1 __id andb orb].

Ltac subst_sim :=
  repeat lazymatch goal with
         | H : ?F (sim_regs ?Σ) = _ |- context [?F (sim_regs ?Σ)] => rewrite H
         end.

Ltac red_monad_sim :=
  repeat lazymatch goal with
         | |- sim _ _ (_ >>= _) _ _  => apply sim_bind
         | |- sim _ _ (_ >> _) _ _  => apply sim_bind
         | |- sim _ _ (and_boolM _ _) _ _  => apply sim_bind
         | |- sim _ _ (try_catch _ _) _ _  => apply sim_try_catch
         | |- sim _ _ (Done _) (BindMCtx _ _) _  => apply sim_pop_bind_Done
         | |- sim _ _ (Done _) (TryMCtx _ _) _  => apply sim_pop_try_Done
         | |- sim _ _ (returnm _) (BindMCtx _ _) _  => apply sim_pop_bind_Done
         | |- sim _ _ (returnm _) (TryMCtx _ _) _  => apply sim_pop_try_Done
         end.

Ltac red_sim :=
    repeat first [
        progress cbn_sim |
        progress subst_sim |
        progress reduce_closed_sim |
        progress red_monad_sim
      ].

Lemma sim_undefined_AddressDescriptor n Σ e2 K:
  (∀ a, sim n Σ (Done a) K e2) →
  sim n Σ (undefined_AddressDescriptor ()) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_undefined_InterruptReq n Σ e2 K:
  (∀ a, sim n Σ (Done a) K e2) →
  sim n Σ (undefined_InterruptReq ()) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_undefined_TLBRecord n Σ e2 K:
  (∀ a, sim n Σ (Done a) K e2) →
  sim n Σ (undefined_TLBRecord ()) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_undefined_bitvector E n Σ z F e2 K:
  (∀ b, sim n Σ (Done b) K e2) →
  sim (E:=E) n Σ (@undefined_bitvector _ _ z F) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_undefined_bool E n Σ e2 K:
  (∀ b, sim n Σ (Done b) K e2) →
  sim (E:=E) n Σ (undefined_bool ()) K e2.
Proof.
  move => Hsim.
  apply: sim_Choose.
Admitted.

Lemma sim_undefined_LogicalOp n Σ e2 K:
  (∀ op, sim n Σ (Done op) K e2) →
  sim n Σ (undefined_LogicalOp ()) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_IsSecure n Σ e2 K:
  sim n Σ (Done false) K e2 →
  sim n Σ (IsSecure ()) K e2.
Proof.
Admitted.

Lemma sim_DebugTargetFrom n Σ e2 K:
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (DebugTargetFrom false) K e2.
Proof.
Admitted.

Lemma sim_ELUsingAArch32 n Σ e2 K el:
  sim n Σ (Done false) K e2 →
  sim n Σ (ELUsingAArch32 el) K e2.
Proof.
Admitted.

Lemma sim_UsingAArch32 n Σ e2 K:
  sim n Σ (Done false) K e2 →
  sim n Σ (UsingAArch32 ()) K e2.
Proof.
Admitted.

Lemma sim_S1TranslationRegime__1 n Σ e2 K:
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (S1TranslationRegime__1 ()) K e2.
Proof.
Admitted.

Lemma sim_HasS2Translation n Σ e2 K:
  sim n Σ (Done true) K e2 →
  sim n Σ (HasS2Translation ()) K e2.
Proof.
  move => Hsim.
  unfold HasS2Translation. red_sim.
Admitted.

Lemma sim_AArch64_GenerateDebugExceptions n Σ e2 K:
  sim n Σ (Done false) K e2 →
  sim n Σ (AArch64_GenerateDebugExceptions ()) K e2.
Proof.
Admitted.

Lemma sim_CheckSoftwareStep n Σ e2 K:
  sim n Σ (Done tt) K e2 →
  sim n Σ (CheckSoftwareStep ()) K e2.
Proof.
  move => Hsim.
  unfold CheckSoftwareStep, DebugTarget. red_sim.
  apply: sim_IsSecure. red_sim.
  apply: sim_DebugTargetFrom => ?. red_sim.
  apply: sim_ELUsingAArch32. red_sim.
  apply: sim_AArch64_GenerateDebugExceptions. red_sim.
  done.
Qed.

Lemma sim_BranchTargetCheck n Σ e2 K:
  sim n Σ (Done tt) K e2 →
  sim n Σ (BranchTargetCheck ()) K e2.
Proof.
  move => Hsim. unfold BranchTargetCheck.
Admitted.

Lemma sim_PostDecode n Σ e2 K:
  sim n Σ (Done tt) K e2 →
  sim n Σ (__PostDecode ()) K e2.
Proof.
  move => Hsim.
  unfold __PostDecode. red_sim.
  apply: sim_UsingAArch32. red_sim.
  by apply: sim_BranchTargetCheck.
Qed.

Lemma sim_AArch64_CheckPCAlignment n Σ e2 K:
  sim n Σ (Done tt) K e2 →
  sim n Σ (AArch64_CheckPCAlignment ()) K e2.
Proof. Admitted.

Lemma sim_AArch64_TranslateAddressS1Off n Σ e2 K a acctype iswrite:
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (AArch64_TranslateAddressS1Off a acctype iswrite) K e2.
Proof.
  move => Hsim.
  (* unfold AArch64_TranslateAddressS1Off. *)
  (* red_sim. *)
  (* apply: sim_S1TranslationRegime__1 => ?. red_sim. *)
  (* apply sim_ELUsingAArch32. => ?. red_sim. *)
Admitted.

Lemma sim_AArch64_FirstStageTranslate n Σ e2 size K a al acctype iswrite:
  acctype ≠ AccType_NV2REGISTER →
  HCR_EL2 (sim_regs Σ) = (Ox"0000000000000000" : mword 64) →
  SCTLR_EL1 (sim_regs Σ) = (Ox"0000000004000002" : mword 64) →
    (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (AArch64_FirstStageTranslate a acctype iswrite al size) K e2.
Proof.
  move => ? HHCR_EL2 HSCTLR_EL1 Hsim.
  unfold AArch64_FirstStageTranslate. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
  case_match. { admit. } red_sim.
  apply: sim_HasS2Translation. red_sim.
  apply: sim_read_reg; [done|] => ??. red_sim.
  apply: sim_read_reg; [done|] => ??. red_sim.
  apply: sim_read_reg; [done|] => ??. red_sim.
  apply: sim_undefined_bitvector => ?. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
  apply: sim_undefined_TLBRecord => ?. red_sim.
  apply: sim_undefined_bitvector => ?. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
  apply: sim_AArch64_TranslateAddressS1Off => ?. red_sim.
  apply: sim_UsingAArch32. red_sim.
Admitted.

Lemma sim_AArch64_FullTranslate n Σ e2 size K a al acctype iswrite:
  acctype ≠ AccType_NV2REGISTER →
  HCR_EL2 (sim_regs Σ) = (Ox"0000000000000000" : mword 64) →
  SCTLR_EL1 (sim_regs Σ) = (Ox"0000000004000002" : mword 64) →
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (AArch64_FullTranslate a acctype iswrite al size) K e2.
Proof.
  move => ??? Hsim.
  unfold AArch64_FullTranslate. red_sim.
  apply: sim_AArch64_FirstStageTranslate; [done..|] => ?. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
  apply: sim_undefined_AddressDescriptor => ?. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
Admitted.

Lemma sim_AArch64_TranslateAddress n Σ e2 size K a al acctype iswrite:
  acctype ≠ AccType_NV2REGISTER →
  HCR_EL2 (sim_regs Σ) = (Ox"0000000000000000" : mword 64) →
  SCTLR_EL1 (sim_regs Σ) = (Ox"0000000004000002" : mword 64) →
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (AArch64_TranslateAddress a acctype iswrite al size) K e2.
Proof.
  move => ??? Hsim.
  unfold AArch64_TranslateAddress. red_sim.
  apply: sim_undefined_AddressDescriptor => ?. red_sim.
  apply: sim_AArch64_FullTranslate; [done..|] => ?. red_sim.
Admitted.


Lemma sim_AArch64_aget_MemSingle n Σ e2 size K a al acctype F:
  acctype ≠ AccType_NV2REGISTER →
  HCR_EL2 (sim_regs Σ) = (Ox"0000000000000000" : mword 64) →
  SCTLR_EL1 (sim_regs Σ) = (Ox"0000000004000002" : mword 64) →
  (∀ v, sim n Σ (Done v) K e2) →
  sim n Σ (@AArch64_aget_MemSingle a size acctype al F) K e2.
Proof.
  move => ??? Hsim.
  unfold AArch64_aget_MemSingle. red_sim.
  apply: sim_assert_exp'. { shelve. } move => ?. red_sim.
  apply: sim_assert_exp. { shelve. } red_sim.
  apply: sim_undefined_AddressDescriptor => ?. red_sim.
  apply: sim_undefined_bitvector => ?. red_sim.
  apply: sim_AArch64_TranslateAddress; [done..|] => ?. red_sim.
Admitted.

Lemma sim_fetchA64 n Σ K e2 op t:
  Σ.(sim_instrs) !! (mword_to_bv (_PC Σ.(sim_regs))) = Some (op, t) →
  sim n Σ (Done (bv_to_mword op)) K e2 →
  sim n Σ (__fetchA64 ()) K  e2.
Proof.
  move => Hinstrs Hsim.
  unfold __fetchA64. red_sim.
  apply: sim_CheckSoftwareStep. red_sim.
  apply: sim_AArch64_CheckPCAlignment. red_sim.
  apply: sim_read_reg; [done|]. move => ? _. red_sim.
Admitted.

Lemma sim_TakePendingInterrupts n Σ K e2 r:
  sim n Σ (Done false) K e2 →
  sim n Σ (TakePendingInterrupts r) K e2.
Proof.
  move => Hsim.
Admitted.

Lemma sim_example n regs:
  ProcState_nRW (PSTATE regs) = ('b "0" : mword 1) →
  sim n (SIM regs test_mapped_regs ∅ test_instrs) (Done tt) NilMCtx [].
Proof.
  move => HnRW.
  apply: sim_Step_CPU => ? _.
  unfold Step_CPU. red_sim.
  apply: sim_undefined_InterruptReq => ?. red_sim.
  apply: sim_TakePendingInterrupts. red_sim.
  apply: sim_read_reg; [done|] => ??. red_sim. rewrite HnRW. red_sim.
  apply: sim_fetchA64. { simpl. admit. } red_sim.
  apply: sim_write_reg; [done|] => ??. unfold set. red_sim.
  apply: sim_write_reg; [done|] => ??. unfold set. red_sim.
  apply: sim_read_reg; [done|] => ??.
Admitted.


Definition decode_integer_logical_shiftedreg_decode (op_code : mword 32) :=
  (
 (and_boolM
       (returnm ((andb
                    (eq_vec (subrange_vec_dec op_code 30 24) ( 'b"0101010"  : mword (30 - (24 - 1))))
                    (eq_vec (subrange_vec_dec op_code 21 21) ('b"0"  : mword (21 - (21 - 1)))))
         : bool)) (read_reg SEE_ref >>= fun w__1664 : Z => returnm ((Z.ltb w__1664 1858)  : bool))) >>= fun w__1665 : bool =>
    if sumbool_of_bool w__1665 then
      write_reg SEE_ref 1858 >>
      let Rd : bits 5 := subrange_vec_dec op_code 4 0 in
      let Rn : bits 5 := subrange_vec_dec op_code 9 5 in
      let imm6 : bits 6 := subrange_vec_dec op_code 15 10 in
      let Rm : bits 5 := subrange_vec_dec op_code 20 16 in
      let N : bits 1 := (vec_of_bits [access_vec_dec op_code 21]  : mword 1) in
      let shift : bits 2 := subrange_vec_dec op_code 23 22 in
      let opc : bits 2 := subrange_vec_dec op_code 30 29 in
      let sf : bits 1 := (vec_of_bits [access_vec_dec op_code 31]  : mword 1) in
      (integer_logical_shiftedreg_decode Rd Rn imm6 Rm N shift opc sf)
       : M (unit)
    else
 Fail "a").

(* Eval hnf in (decode64 (Pos.to_nat 32 'h "AA0303F3" : mword 32)). *)

Lemma test n regs:
  SEE regs = 0 →
  sim n (SIM regs test_mapped_regs ∅ test_instrs) (decode_integer_logical_shiftedreg_decode (Ox"AA0303F3" : mword 32)) NilMCtx [].
  (* sim n (SIM regs test_mapped_regs ∅ test_instrs) (decode64 (Ox"AA0303F3" : mword 32)) NilMCtx []. *)
Proof.
  move => HSEE.
  unfold decode_integer_logical_shiftedreg_decode. red_sim.
  apply: sim_read_reg; [done|] => ??. red_sim. rewrite HSEE. red_sim.
  apply: sim_write_reg; [done|] => ??. red_sim. unfold set. red_sim.
  unfold integer_logical_shiftedreg_decode. red_sim.
  apply: sim_write_reg; [done|] => ??. unfold set. red_sim.
  apply: sim_undefined_bool => ?. red_sim.
  apply: sim_undefined_LogicalOp => ?. red_sim.
  unfold DecodeShift. red_sim.
  apply: sim_PostDecode. red_sim.
  unfold integer_logical_shiftedreg. red_sim.
  unfold aget_X. red_sim.
  unfold ShiftReg, aget_X. red_sim.
  apply: sim_read_reg. { admit. } move => ??. red_sim.
  unfold LSL. red_sim.
  (* cbn [uint projT1 uint_plain Word.wordToN]. *)
Abort.
