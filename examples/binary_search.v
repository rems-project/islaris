Require Import isla.base.
Require Import isla.opsem.
Require Import isla.automation.
Require Import isla.adequacy.
Require Import isla.examples.sys_regs.
From isla.instructions.binary_search Require Import instrs.


(*
The code can be generated with
PATH=$PWD/bin:$PATH dune exec -- isla-coq examples/binary_search.dump -d -o instructions/binary_search  -n "a{addr}" --coqdir=isla.instructions.binary_search

*)

Definition binary_search_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (tmp src dst i n : bv 64) (srcdata dstdata : list byte) (pstaten pstatez pstatec pstatev : bv 1),
  reg_col sys_regs ∗
  "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
  "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
  "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
  "R3" ↦ᵣ Val_Bits i ∗ "R4" ↦ᵣ Val_Bits tmp ∗
  src ↦ₘ∗ srcdata ∗ dst ↦ₘ∗ dstdata ∗
  instr_pre 0x0000000010300054 (
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

Arguments binary_search_loop_spec /.

Lemma binary_search_loop `{!islaG Σ} `{!threadG} :
  instr 0x000000001030002c (Some a2c) -∗
  instr 0x0000000010300030 (Some a30) -∗
  instr 0x0000000010300034 (Some a34) -∗
  instr 0x0000000010300038 (Some a38) -∗
  instr 0x000000001030003c (Some a3c) -∗
  instr 0x0000000010300040 (Some a40) -∗
  instr 0x0000000010300044 (Some a44) -∗
  instr 0x0000000010300048 (Some a48) -∗
  instr 0x000000001030004c (Some a4c) -∗
  instr 0x0000000010300050 (Some a50) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x000000001030002c binary_search_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
Abort.

Lemma binary_search `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr 0x0000000010300020 (Some a20) -∗
  instr 0x0000000010300024 (Some a24) -∗
  instr 0x0000000010300028 (Some a28) -∗

  instr 0x0000000010300054 (Some a54) -∗
  instr 0x0000000010300058 (Some a58) -∗
  instr 0x000000001030005c (Some a5c) -∗
  instr 0x0000000010300060 (Some a60) -∗
  instr 0x0000000010300064 (Some a64) -∗
  instr 0x0000000010300068 (Some a68) -∗
  instr 0x000000001030006c (Some a6c) -∗
  instr 0x0000000010300070 (Some a70) -∗
  □ instr_pre 0x000000001030002c binary_search_loop_spec -∗
  instr_body 0x0000000010300000 (
    ∃ (tmp1 tmp2 src dst n ret : bv 64) (srcdata dstdata : list byte) (pstaten pstatez pstatec pstatev : bv 1),
    reg_col sys_regs ∗
    "PSTATE" # "N" ↦ᵣ Val_Bits pstaten ∗ "PSTATE" # "Z" ↦ᵣ Val_Bits pstatez ∗
    "PSTATE" # "C" ↦ᵣ Val_Bits pstatec ∗ "PSTATE" # "V" ↦ᵣ Val_Bits pstatev ∗
    "R0" ↦ᵣ Val_Bits dst ∗ "R1" ↦ᵣ Val_Bits src ∗ "R2" ↦ᵣ Val_Bits n ∗
    "R3" ↦ᵣ Val_Bits tmp2 ∗ "R4" ↦ᵣ Val_Bits tmp1 ∗
    "R30" ↦ᵣ Val_Bits ret ∗
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
Abort.
