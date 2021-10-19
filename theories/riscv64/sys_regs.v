Require Import isla.base.
Require Import isla.automation.

(* this should encode MXL 2 and extensions A,C,D,F,I,M,N,Q,S,U
  0b1000000000000000000000000000000000000000000101010011000100101101
*)
Definition misa_bits : bv 64 :=
  [BV{64}0x800000000015312d].

Definition sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp" , ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access" , ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base" , ExactShape (RVal_Bits [BV{64} 0x0000000080000000]));
  (KindReg "rv_ram_size" , ExactShape (RVal_Bits [BV{64} 0x0000000004000000]));
  (KindReg "rv_rom_base" , ExactShape (RVal_Bits [BV{64} 0x0000000000001000]));
  (KindReg "rv_rom_size" , ExactShape (RVal_Bits [BV{64} 0x0000000000000100]));
  (KindReg "rv_clint_base" , ExactShape (RVal_Bits [BV{64} 0x0000000002000000]));
  (KindReg "rv_clint_size" , ExactShape (RVal_Bits [BV{64} 0x00000000000c0000]));
  (KindReg "rv_htif_tohost" , ExactShape (RVal_Bits [BV{64} 0x0000000040001000]));
  (KindReg "cur_privilege" , ExactShape (RVal_Enum (Mk_enum_id 3, Mk_enum_ctor 2)));
  (* TODO: remove this *)
  (KindReg "Machine" , ExactShape (RVal_Enum (Mk_enum_id 3, Mk_enum_ctor 2)));
  (KindReg "misa" , ExactShape (RegVal_Struct [("bits", RVal_Bits misa_bits)]));
  (KindReg "mstatus" , StructShape [("bits",  PropShape (λ v,
           (* MPRV disabled *)
           ∃ b : bv 64, v = RVal_Bits b ∧ bv_extract 17 1 b = [BV{1} 0]))]);
  (KindReg "satp" , BitsShape 64)
].

Definition sys_regs_map (mstatus_bits satp : bv 64) : reg_map :=
  <[ "rv_enable_pmp" := RVal_Bool false ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool false ]> $
  <[ "rv_ram_base" := RVal_Bits [BV{64} 0x0000000080000000] ]> $
  <[ "rv_ram_size" := RVal_Bits [BV{64} 0x0000000004000000] ]> $
  <[ "rv_rom_base" := RVal_Bits [BV{64} 0x0000000000001000] ]> $
  <[ "rv_rom_size" := RVal_Bits [BV{64} 0x0000000000000100] ]> $
  <[ "rv_clint_base" := RVal_Bits [BV{64} 0x0000000002000000] ]> $
  <[ "rv_clint_size" := RVal_Bits [BV{64} 0x00000000000c0000] ]> $
  <[ "rv_htif_tohost" := RVal_Bits [BV{64} 0x0000000040001000] ]> $
  <[ "cur_privilege" := RVal_Enum (Mk_enum_id 3, Mk_enum_ctor 2) ]> $
  <[ "Machine" := RVal_Enum (Mk_enum_id 3, Mk_enum_ctor 2) ]> $
  <[ "misa" := RegVal_Struct [("bits", RVal_Bits misa_bits)] ]> $
  <[ "mstatus" := RegVal_Struct [("bits", RVal_Bits mstatus_bits)] ]> $
  <[ "satp" := RVal_Bits satp ]> $
  ∅.

Section sys_regs.
  Context `{!islaG Σ} `{!threadG}.

  Lemma sys_regs_init mstatus_bits satp regs:
    bv_extract 17 1 mstatus_bits = [BV{1} 0] →
    regs_ctx regs -∗
    ([∗ map] k↦y ∈ sys_regs_map mstatus_bits satp, k ↦ᵣ y) ==∗
    regs_ctx regs ∗
    reg_col sys_regs.
  Proof.
    move => ?.
    repeat (rewrite big_sepM_insert;[ | by vm_compute]).
    iIntros "Hctx H".
    simpl. iModIntro. rewrite -(right_id True%I _ (reg_col sys_regs)).
    iRevert "H". repeat liAStep; liShow.
    Unshelve. all: prepare_sidecond.
    naive_solver.
  Qed.
End sys_regs.
