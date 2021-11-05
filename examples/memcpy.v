Require Import isla.aarch64.aarch64.
From isla.instructions.memcpy Require Import instrs.


(*
C code:
    void mcpy(unsigned char *dest, unsigned char *src, size_t n) {
      for(size_t i = 0; i < n; i++ ) {
        dest[i] = src[i];
      }
    }

ASM:
0000000000000000 <mcpy>:
   0:	b40000e2 	cbz	x2, 1c <mcpy+0x1c>
   4:	d2800003 	mov	x3, #0x0                   	// #0
   8:	38636824 	ldrb	w4, [x1, x3]
   c:	38236804 	strb	w4, [x0, x3]
  10:	91000463 	add	x3, x3, #0x1
  14:	eb03005f 	cmp	x2, x3
  18:	54ffff81 	b.ne	8 <mcpy+0x8>  // b.any
  1c:	d65f03c0 	ret

The code can be generated with
$ PATH=$PWD/bin:$PATH dune exec -- isla-coq examples/memcpy.dump -d -o instructions  -n "a{op}" --coqdir=isla.instructions

*)

Definition memcpy_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst i n : bv 64) (srcdata dstdata : list byte),
  reg_col sys_regs ∗
  reg_col CNVZ_regs ∗
  "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
  "R3" ↦ᵣ RVal_Bits i ∗ "R4" ↦ᵣ RVal_Bits tmp ∗
  bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
  ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
  ⌜bv_unsigned i < bv_unsigned n⌝ ∗
  ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜take (Z.to_nat (bv_unsigned i)) dstdata = take (Z.to_nat (bv_unsigned i)) srcdata⌝ ∗
  instr_pre 0x000000001030001c (
    ∃ (tmp n : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
      "R4" ↦ᵣ RVal_Bits tmp ∗ "R3" ↦ᵣ RVal_Bits n ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
  )
.

Arguments memcpy_loop_spec /.

Lemma memcpy_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  □ instr_pre 0x0000000010300008 memcpy_loop_spec -∗
  instr_body 0x0000000010300008 memcpy_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned i)).
  Time repeat liAStep; liShow.
  liInst Hevar (Z.to_nat (bv_unsigned i)).
  Time repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try bv_simplify_arith_hyp select (bv_extract _ _ _ ≠ _).
  all: try bv_simplify_arith_hyp select (bv_extract _ _ _ = _).
  - rewrite insert_length. bv_solve.
  - bv_solve.
  - bv_simplify.
    rewrite (bv_wrap_small _ (bv_unsigned i)); [|bv_solve].
    rewrite (bv_wrap_small _ (bv_unsigned i + _)); [|bv_solve].
    have ->: (Z.to_nat (bv_unsigned i + 1)) = S ((Z.to_nat (bv_unsigned i))) by bv_solve.
    erewrite take_S_r. 2: apply list_lookup_insert; bv_solve.
    erewrite take_S_r; [|done].
    rewrite take_insert; [|lia].
    f_equal; [done|]. f_equal. bv_solve.
  - bv_solve.
  - rewrite -(take_drop (Z.to_nat (bv_unsigned i)) (<[_ := _]> dstdata)).
    rewrite -(take_drop (Z.to_nat (bv_unsigned i)) srcdata).
    f_equal.
    + by rewrite take_insert.
    + erewrite drop_S. 2: { apply: list_lookup_insert. bv_solve. }
      erewrite (drop_S srcdata); [|done].
      rewrite !drop_ge ?insert_length; [ |bv_solve..].
      f_equal. bv_solve.
Qed.

Lemma memcpy `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x000000001030001c (Some a1c) -∗
  □ instr_pre 0x0000000010300008 memcpy_loop_spec -∗
  instr_body 0x0000000010300000 (
    ∃ (tmp1 tmp2 src dst n ret : bv 64) (srcdata dstdata : list byte),
    reg_col sys_regs ∗
    reg_col CNVZ_regs ∗
    "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
    "R3" ↦ᵣ RVal_Bits tmp2 ∗ "R4" ↦ᵣ RVal_Bits tmp1 ∗
    "R30" ↦ᵣ RVal_Bits ret ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
    ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp1 tmp2 n : bv 64),
      reg_col sys_regs ∗
      reg_col CNVZ_regs ∗
      "R0" ↦ᵣ RVal_Bits dst ∗ "R1" ↦ᵣ RVal_Bits src ∗ "R2" ↦ᵣ RVal_Bits n ∗
      "R3" ↦ᵣ RVal_Bits tmp2 ∗ "R4" ↦ᵣ RVal_Bits tmp1 ∗
      "R30" ↦ᵣ RVal_Bits ret ∗
      bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
      True
  )).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  - by destruct dstdata, srcdata.
  - bv_simplify_hyp select (n ≠ _). bv_solve.
Time Qed.
