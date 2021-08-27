Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.examples.sys_regs.
From isla.instructions Require Import a38236804 a38636824 a54ffff81 a91000463 ab40000e2 ad2800003 ad65f03c0 aeb03005f.


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
*)

Definition memcpy_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst i n : bv 64) (srcdata dstdata : list byte) (pstaten pstatez pstatec pstatev : bv 1),
  reg_col sys_regs ∗
  "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
  "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
  "R3" ↦ᵣ Val_Bits i ∗ "R4" ↦ᵣ Val_Bits tmp ∗
  src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ dstdata ∗
  ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
  ⌜bv_unsigned i < bv_unsigned n⌝ ∗
  ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
  ⌜take (Z.to_nat (bv_unsigned i)) dstdata = take (Z.to_nat (bv_unsigned i)) srcdata⌝ ∗
  instr_pre 0x000000001030001c (
    ∃ (tmp n : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
      reg_col sys_regs ∗
      "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
      "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
      "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
      "R4" ↦ᵣ Val_Bits tmp ∗ "R3" ↦ᵣ Val_Bits n ∗
      src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ srcdata ∗
      True
  )
.

Arguments memcpy_loop_spec /.

Lemma memcpy_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300008 (Some a38636824) -∗
  instr 0x000000001030000c (Some a38236804) -∗
  instr 0x0000000010300010 (Some a91000463) -∗
  instr 0x0000000010300014 (Some aeb03005f) -∗
  instr 0x0000000010300018 (Some a54ffff81) -∗
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
  - rename select (bv_extract _ _ _ ≠ _) into Hextract.
    (* TODO: use some lemma to turn bv_not into bv_opp / bv_sub *)
    admit.
  - admit.
  - admit.
  - admit.
Abort.

Lemma memcpy `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some ab40000e2) -∗
  instr 0x0000000010300004 (Some ad2800003) -∗
  instr 0x000000001030001c (Some ad65f03c0) -∗
  □ instr_pre 0x0000000010300008 memcpy_loop_spec -∗
  instr_body 0x0000000010300000 (
    ∃ (tmp1 tmp2 src dst n ret : bv 64) (srcdata dstdata : list byte) (pstaten pstatez pstatec pstatev : bv 1),
    reg_col sys_regs ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
    "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
    "R3" ↦ᵣ Val_Bits tmp2 ∗ "R4" ↦ᵣ Val_Bits tmp1 ∗
    "R30" ↦ᵣ Val_Bits ret ∗
    src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗ ⌜bv_unsigned n = length dstdata⌝ ∗
    ⌜bv_unsigned src + bv_unsigned n < 2 ^ 52⌝ ∗
    ⌜bv_unsigned dst + bv_unsigned n < 2 ^ 52⌝ ∗
    instr_pre (bv_unsigned ret) (
    ∃ (tmp1 tmp2 n : bv 64) (pstaten pstatez pstatec pstatev : bv 1),
      reg_col sys_regs ∗
      "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
      "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
      "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
      "R3" ↦ᵣ Val_Bits tmp2 ∗ "R4" ↦ᵣ Val_Bits tmp1 ∗
      "R30" ↦ᵣ Val_Bits ret ∗
      src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ srcdata ∗
      True
  )).
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  - by destruct dstdata, srcdata.
  - bv_simplify_hyp select (n ≠ _). bv_solve.
Time Qed.
