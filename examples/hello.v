Require Import isla.aarch64.aarch64.
From isla.instructions.hello Require Import instrs.

(*
C code:
	char *string = "Hello, World!\n";
	while(*string) {
		*(volatile char *)0x101f1000 = *string;
		string++;
	}

ASM:
.LC0:
        .string "Hello, World!\n"
main:
        adrp    x1, .LC0
        mov     x2, 4096
        add	    x1, x1, #0x690
        mov     w0, 72
        movk    x2, 0x101f, lsl 16
.L2:
        strb    w0, [x2]
        ldrb    w0, [x1, 1]!
        cbnz    w0, .L2
*)

Definition hello_world_string : list byte :=
  [ [BV{8} 0x48]; [BV{8} 0x65]; [BV{8} 0x6c]; [BV{8} 0x6c];  [BV{8} 0x6f]; [BV{8} 0x2c]; [BV{8} 0x20]; [BV{8} 0x57];  [BV{8} 0x6f]; [BV{8} 0x72]; [BV{8} 0x6c]; [BV{8} 0x64]; [BV{8} 0x21]; [BV{8} 0x0a]; [BV{8} 0x00]].

Definition hello_world_string_printed : list byte :=
  take (length hello_world_string - 1) hello_world_string.

Definition hello_spec_trace : list seq_label → Prop :=
  sapp ((λ b : byte, SWriteMem [BV{64} 0x101f1000] b) <$> hello_world_string_printed) $
  scons (SInstrTrap [BV{64} 0x0000000010300020]) $
  snil.

Definition hello_loop_spec `{!islaG Σ} `{!threadG} : iProp Σ :=
  ∃ (i : nat),
  ⌜i + 1 < length hello_world_string⌝ ∗
  reg_col sys_regs ∗
  [BV{64} 0x0000000010300690] ↦ₘ∗ hello_world_string ∗
  "R2" ↦ᵣ RVal_Bits [BV{64} 0x101f1000] ∗
  "R1" ↦ᵣ RVal_Bits (bv_add_Z [BV{64} 0x0000000010300690] i) ∗
  "R0" ↦ᵣ RVal_Bits (bv_zero_extend 64 (hello_world_string !!! i)) ∗
  spec_trace (sapp ((λ b : byte, SWriteMem [BV{64} 0x101f1000] b) <$> (drop i hello_world_string_printed)) $ scons (SInstrTrap [BV{64} 0x0000000010300020]) snil) ∗
  True
.

Arguments hello_loop_spec /.

Lemma hello_loop `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300014 (Some a14) -∗
  instr 0x0000000010300018 (Some a18) -∗
  instr 0x000000001030001c (Some a1c) -∗
  instr 0x0000000010300020 None -∗
  □ instr_pre 0x0000000010300014 hello_loop_spec -∗
  mmio_range [BV{64} 0x101f1000] 0x10 -∗
  instr_body 0x0000000010300014 hello_loop_spec.
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  erewrite drop_S; csimpl.
  2: { apply: list_lookup_lookup_total_lt => /=. lia. }
  Time repeat liAStep; liShow.
  liInst Hevar (S i)%nat.
  Time repeat liAStep; liShow.
  liInst Hevar (S i)%nat.
  Time repeat liAStep; liShow.

  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  - rewrite lookup_total_take /=; [|lia]. bv_solve.
  - have ? : i = 13%nat. {
      rename select (bv_concat _ _ _ = _) into Heq.
      revert select (_ !! i = Some vmem). move: Heq. clear => ??.
      by repeat (destruct i; simplify_eq/=).
    }
    subst. rewrite drop_ge //. normalize_and_simpl_goal => //. bv_solve.
  - rename select (bv_concat _ _ _ ≠ _) into Hneq.
    bv_simplify_hyp Hneq.
    revert select (_ !! i = Some vmem). move: Hneq. clear => ??.
    by repeat (destruct i; simplify_eq/=).
  - erewrite list_lookup_total_correct; [|done]. bv_solve.
Time Qed.


Lemma hello `{!islaG Σ} `{!threadG} :
  instr 0x0000000010300000 (Some a0) -∗
  instr 0x0000000010300004 (Some a4) -∗
  instr 0x0000000010300008 (Some a8) -∗
  instr 0x000000001030000c (Some ac) -∗
  instr 0x0000000010300010 (Some a10) -∗
  □ instr_pre 0x0000000010300014 hello_loop_spec -∗
  instr_body 0x0000000010300000 (
    reg_col sys_regs ∗
    [BV{64} 0x0000000010300690] ↦ₘ∗ hello_world_string ∗
    "_PC" ↦ᵣ RVal_Bits [BV{64} 0x0000000010300000 - 0x4] ∗
    "__PC_changed" ↦ᵣ RVal_Bool false ∗
    "R0" ↦ᵣ RegVal_Poison ∗
    "R1" ↦ᵣ RegVal_Poison ∗
    "R2" ↦ᵣ RegVal_Poison ∗
    "R11" ↦ᵣ RegVal_Poison ∗
    spec_trace hello_spec_trace ∗
    True)
    .
Proof.
  iStartProof.
  Time repeat liAStep; liShow.
  liInst Hevar 0%nat.
  Time repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: bv_simplify; try done.
Time Qed.
