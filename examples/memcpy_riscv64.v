Require Import isla.riscv64.riscv64.
From isla.instructions.memcpy_riscv64 Require Import instrs.

(* #[export] Hint Rewrite @insert_length : bv_simplify. *)

Definition memcpy_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst n : bv 64) (srcdata dstdata : list byte) (i : nat),
  reg_col sys_regs ∗
  "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗ "x12" ↦ᵣ RVal_Bits n ∗
  "x13" ↦ᵣ RVal_Bits tmp ∗
  (bv_unsigned src - i) ↦ₘ∗ srcdata ∗ (bv_unsigned dst - i) ↦ₘ∗ dstdata ∗
  ⌜(bv_unsigned n + i)%Z = length srcdata⌝ ∗ ⌜(bv_unsigned n + i)%Z = length dstdata⌝ ∗
  ⌜0 < bv_unsigned n⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned dst ∧ bv_unsigned dst + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜0x0000000080000000 ≤ bv_unsigned src ∧ bv_unsigned src + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
  ⌜take i dstdata = take i srcdata⌝ ∗
  instr_pre 0x000000001030001c (
    ∃ (tmp : bv 64),
      reg_col sys_regs ∗
      "x10" ↦ᵣ RVal_Bits (bv_add dst n) ∗
      "x11" ↦ᵣ RVal_Bits (bv_add src n) ∗ "x12" ↦ᵣ RVal_Bits [BV{64} 0] ∗
      "x13" ↦ᵣ RVal_Bits tmp ∗
      (bv_unsigned src - i) ↦ₘ∗ srcdata ∗ (bv_unsigned dst - i) ↦ₘ∗ srcdata ∗
      True
  )
.

Arguments memcpy_loop_spec /.

Lemma memcpy_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  □ instr_pre 0x0000000010300004 memcpy_loop_spec -∗
  instr_body 0x0000000010300004 memcpy_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar i.
  Time repeat liAStep; liShow.
  liInst Hevar i.
  Time repeat liAStep; liShow.
  liInst Hevar5 (S i).
  Time repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  all: try bv_simplify_hyp select (bv_add n _ = _).
  all: try bv_simplify_hyp select (bv_add n _ ≠ _).
  all: try rewrite insert_length.
  all: try bv_solve.
  - rewrite -(take_drop i (<[_ := _]> dstdata)).
    rewrite -(take_drop i srcdata).
    f_equal.
    + by rewrite take_insert.
    + erewrite drop_S. 2: { apply: list_lookup_insert. bv_solve. }
      erewrite (drop_S srcdata); [|done].
      rewrite !drop_ge ?insert_length //; [ |bv_solve..].
      f_equal. bv_solve.
  - erewrite take_S_r. 2: apply list_lookup_insert; bv_solve.
    erewrite take_S_r; [|done].
    rewrite take_insert; [|lia].
    f_equal; [done|]. f_equal. bv_solve.
Qed.

Lemma memcpy `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300004 memcpy_loop_spec -∗
  instr_body 0x0000000010300000 (
    ∃ (tmp src dst n ret : bv 64) (srcdata dstdata : list byte),
    reg_col sys_regs ∗
    "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗ "x12" ↦ᵣ RVal_Bits n ∗
    "x13" ↦ᵣ RVal_Bits tmp ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned dst ∧ bv_unsigned dst + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    ⌜0x0000000080000000 ≤ bv_unsigned src ∧ bv_unsigned src + bv_unsigned n < 0x0000000080000000 + 0x0000000004000000⌝ ∗
    ⌜bv_extract 0 1 ret = [BV{1} 0]⌝ ∗ ⌜bv_extract 1 1 ret = [BV{1} 0]⌝ ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp : bv 64),
      reg_col sys_regs ∗
      "x10" ↦ᵣ RVal_Bits (bv_add dst n) ∗ "x11" ↦ᵣ RVal_Bits (bv_add src n) ∗ "x12" ↦ᵣ RVal_Bits [BV{64} 0] ∗
      "x13" ↦ᵣ RVal_Bits tmp ∗
      "x1" ↦ᵣ RVal_Bits ret ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
  )).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar5 0%nat.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - by destruct dstdata, srcdata.
  - bv_simplify_hyp select (n ≠ _). bv_solve.
Time Qed.
