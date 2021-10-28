Require Export Sail.Base.
Require Export Sail.Prompt_monad.
Require Export RV64.riscv_types.
Require Export RV64.mem_metadata.
Require Export RV64.riscv_extras.
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
    minstret_written := minstret_written regs;
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
  |}.
Proof. now destruct regs. Qed.

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
Require Import isla.base.

(* This file should not depend on anything in isla-coq since it is quite slow to compile. *)

Lemma get_word_word_binop {n} f (b1 b2 : mword n):
  get_word (word_binop f b1 b2) = f _ (get_word b1) (get_word b2).
Proof. by destruct n. Qed.

Lemma get_word_to_word n H (w : Word.word (Z.to_nat n)):
  get_word (to_word H w) = w.
Proof. destruct n => //. Qed.

Lemma get_word_inj n (m1 m2 : mword n):
  get_word m1 = get_word m2 → m1 = m2.
Proof. by destruct n. Qed.

Lemma lt_Npow2 n n1:
  (0 ≤ n1)%Z →
  (n < NatLib.Npow2 (Z.to_nat n1))%N ↔ (Z.of_N n < 2 ^ n1)%Z.
Proof.
  move => ?.
  rewrite -Npow2_pow Z_nat_N. etrans; [ apply N2Z.inj_lt |].
  by rewrite N2Z.inj_pow Z2N.id.
Qed.
(*
Definition get_regval' (reg_name : string) (s : regstate) : option register_value :=
  match reg_name with
  | "satp" => Some (satp_ref.(regval_of) (satp_ref.(read_from) s))
  | "tlb48" => Some (tlb48_ref.(regval_of) (tlb48_ref.(read_from) s))
  | "tlb39" => Some (tlb39_ref.(regval_of) (tlb39_ref.(read_from) s))
  | "htif_payload_writes" => Some (htif_payload_writes_ref.(regval_of) (htif_payload_writes_ref.(read_from) s))
  | "htif_cmd_write" => Some (htif_cmd_write_ref.(regval_of) (htif_cmd_write_ref.(read_from) s))
  | "htif_exit_code" => Some (htif_exit_code_ref.(regval_of) (htif_exit_code_ref.(read_from) s))
  | "htif_done" => Some (htif_done_ref.(regval_of) (htif_done_ref.(read_from) s))
  | "htif_tohost" => Some (htif_tohost_ref.(regval_of) (htif_tohost_ref.(read_from) s))
  | "mtimecmp" => Some (mtimecmp_ref.(regval_of) (mtimecmp_ref.(read_from) s))
  | "fcsr" => Some (fcsr_ref.(regval_of) (fcsr_ref.(read_from) s))
  | "f31" => Some (f31_ref.(regval_of) (f31_ref.(read_from) s))
  | "f30" => Some (f30_ref.(regval_of) (f30_ref.(read_from) s))
  | "f29" => Some (f29_ref.(regval_of) (f29_ref.(read_from) s))
  | "f28" => Some (f28_ref.(regval_of) (f28_ref.(read_from) s))
  | "f27" => Some (f27_ref.(regval_of) (f27_ref.(read_from) s))
  | "f26" => Some (f26_ref.(regval_of) (f26_ref.(read_from) s))
  | "f25" => Some (f25_ref.(regval_of) (f25_ref.(read_from) s))
  | "f24" => Some (f24_ref.(regval_of) (f24_ref.(read_from) s))
  | "f23" => Some (f23_ref.(regval_of) (f23_ref.(read_from) s))
  | "f22" => Some (f22_ref.(regval_of) (f22_ref.(read_from) s))
  | "f21" => Some (f21_ref.(regval_of) (f21_ref.(read_from) s))
  | "f20" => Some (f20_ref.(regval_of) (f20_ref.(read_from) s))
  | "f19" => Some (f19_ref.(regval_of) (f19_ref.(read_from) s))
  | "f18" => Some (f18_ref.(regval_of) (f18_ref.(read_from) s))
  | "f17" => Some (f17_ref.(regval_of) (f17_ref.(read_from) s))
  | "f16" => Some (f16_ref.(regval_of) (f16_ref.(read_from) s))
  | "f15" => Some (f15_ref.(regval_of) (f15_ref.(read_from) s))
  | "f14" => Some (f14_ref.(regval_of) (f14_ref.(read_from) s))
  | "f13" => Some (f13_ref.(regval_of) (f13_ref.(read_from) s))
  | "f12" => Some (f12_ref.(regval_of) (f12_ref.(read_from) s))
  | "f11" => Some (f11_ref.(regval_of) (f11_ref.(read_from) s))
  | "f10" => Some (f10_ref.(regval_of) (f10_ref.(read_from) s))
  | "f9" => Some (f9_ref.(regval_of) (f9_ref.(read_from) s))
  | "f8" => Some (f8_ref.(regval_of) (f8_ref.(read_from) s))
  | "f7" => Some (f7_ref.(regval_of) (f7_ref.(read_from) s))
  | "f6" => Some (f6_ref.(regval_of) (f6_ref.(read_from) s))
  | "f5" => Some (f5_ref.(regval_of) (f5_ref.(read_from) s))
  | "f4" => Some (f4_ref.(regval_of) (f4_ref.(read_from) s))
  | "f3" => Some (f3_ref.(regval_of) (f3_ref.(read_from) s))
  | "f2" => Some (f2_ref.(regval_of) (f2_ref.(read_from) s))
  | "f1" => Some (f1_ref.(regval_of) (f1_ref.(read_from) s))
  | "f0" => Some (f0_ref.(regval_of) (f0_ref.(read_from) s))
  | "float_fflags" => Some (float_fflags_ref.(regval_of) (float_fflags_ref.(read_from) s))
  | "float_result" => Some (float_result_ref.(regval_of) (float_result_ref.(read_from) s))
  | "utval" => Some (utval_ref.(regval_of) (utval_ref.(read_from) s))
  | "ucause" => Some (ucause_ref.(regval_of) (ucause_ref.(read_from) s))
  | "uepc" => Some (uepc_ref.(regval_of) (uepc_ref.(read_from) s))
  | "uscratch" => Some (uscratch_ref.(regval_of) (uscratch_ref.(read_from) s))
  | "utvec" => Some (utvec_ref.(regval_of) (utvec_ref.(read_from) s))
  | "pmpaddr15" => Some (pmpaddr15_ref.(regval_of) (pmpaddr15_ref.(read_from) s))
  | "pmpaddr14" => Some (pmpaddr14_ref.(regval_of) (pmpaddr14_ref.(read_from) s))
  | "pmpaddr13" => Some (pmpaddr13_ref.(regval_of) (pmpaddr13_ref.(read_from) s))
  | "pmpaddr12" => Some (pmpaddr12_ref.(regval_of) (pmpaddr12_ref.(read_from) s))
  | "pmpaddr11" => Some (pmpaddr11_ref.(regval_of) (pmpaddr11_ref.(read_from) s))
  | "pmpaddr10" => Some (pmpaddr10_ref.(regval_of) (pmpaddr10_ref.(read_from) s))
  | "pmpaddr9" => Some (pmpaddr9_ref.(regval_of) (pmpaddr9_ref.(read_from) s))
  | "pmpaddr8" => Some (pmpaddr8_ref.(regval_of) (pmpaddr8_ref.(read_from) s))
  | "pmpaddr7" => Some (pmpaddr7_ref.(regval_of) (pmpaddr7_ref.(read_from) s))
  | "pmpaddr6" => Some (pmpaddr6_ref.(regval_of) (pmpaddr6_ref.(read_from) s))
  | "pmpaddr5" => Some (pmpaddr5_ref.(regval_of) (pmpaddr5_ref.(read_from) s))
  | "pmpaddr4" => Some (pmpaddr4_ref.(regval_of) (pmpaddr4_ref.(read_from) s))
  | "pmpaddr3" => Some (pmpaddr3_ref.(regval_of) (pmpaddr3_ref.(read_from) s))
  | "pmpaddr2" => Some (pmpaddr2_ref.(regval_of) (pmpaddr2_ref.(read_from) s))
  | "pmpaddr1" => Some (pmpaddr1_ref.(regval_of) (pmpaddr1_ref.(read_from) s))
  | "pmpaddr0" => Some (pmpaddr0_ref.(regval_of) (pmpaddr0_ref.(read_from) s))
  | "pmp15cfg" => Some (pmp15cfg_ref.(regval_of) (pmp15cfg_ref.(read_from) s))
  | "pmp14cfg" => Some (pmp14cfg_ref.(regval_of) (pmp14cfg_ref.(read_from) s))
  | "pmp13cfg" => Some (pmp13cfg_ref.(regval_of) (pmp13cfg_ref.(read_from) s))
  | "pmp12cfg" => Some (pmp12cfg_ref.(regval_of) (pmp12cfg_ref.(read_from) s))
  | "pmp11cfg" => Some (pmp11cfg_ref.(regval_of) (pmp11cfg_ref.(read_from) s))
  | "pmp10cfg" => Some (pmp10cfg_ref.(regval_of) (pmp10cfg_ref.(read_from) s))
  | "pmp9cfg" => Some (pmp9cfg_ref.(regval_of) (pmp9cfg_ref.(read_from) s))
  | "pmp8cfg" => Some (pmp8cfg_ref.(regval_of) (pmp8cfg_ref.(read_from) s))
  | "pmp7cfg" => Some (pmp7cfg_ref.(regval_of) (pmp7cfg_ref.(read_from) s))
  | "pmp6cfg" => Some (pmp6cfg_ref.(regval_of) (pmp6cfg_ref.(read_from) s))
  | "pmp5cfg" => Some (pmp5cfg_ref.(regval_of) (pmp5cfg_ref.(read_from) s))
  | "pmp4cfg" => Some (pmp4cfg_ref.(regval_of) (pmp4cfg_ref.(read_from) s))
  | "pmp3cfg" => Some (pmp3cfg_ref.(regval_of) (pmp3cfg_ref.(read_from) s))
  | "pmp2cfg" => Some (pmp2cfg_ref.(regval_of) (pmp2cfg_ref.(read_from) s))
  | "pmp1cfg" => Some (pmp1cfg_ref.(regval_of) (pmp1cfg_ref.(read_from) s))
  | "pmp0cfg" => Some (pmp0cfg_ref.(regval_of) (pmp0cfg_ref.(read_from) s))
  | "tselect" => Some (tselect_ref.(regval_of) (tselect_ref.(read_from) s))
  | "stval" => Some (stval_ref.(regval_of) (stval_ref.(read_from) s))
  | "scause" => Some (scause_ref.(regval_of) (scause_ref.(read_from) s))
  | "sepc" => Some (sepc_ref.(regval_of) (sepc_ref.(read_from) s))
  | "sscratch" => Some (sscratch_ref.(regval_of) (sscratch_ref.(read_from) s))
  | "stvec" => Some (stvec_ref.(regval_of) (stvec_ref.(read_from) s))
  | "sideleg" => Some (sideleg_ref.(regval_of) (sideleg_ref.(read_from) s))
  | "sedeleg" => Some (sedeleg_ref.(regval_of) (sedeleg_ref.(read_from) s))
  | "mhartid" => Some (mhartid_ref.(regval_of) (mhartid_ref.(read_from) s))
  | "marchid" => Some (marchid_ref.(regval_of) (marchid_ref.(read_from) s))
  | "mimpid" => Some (mimpid_ref.(regval_of) (mimpid_ref.(read_from) s))
  | "mvendorid" => Some (mvendorid_ref.(regval_of) (mvendorid_ref.(read_from) s))
  | "minstret_written" => Some (minstret_written_ref.(regval_of) (minstret_written_ref.(read_from) s))
  | "minstret" => Some (minstret_ref.(regval_of) (minstret_ref.(read_from) s))
  | "mtime" => Some (mtime_ref.(regval_of) (mtime_ref.(read_from) s))
  | "mcycle" => Some (mcycle_ref.(regval_of) (mcycle_ref.(read_from) s))
  | "mcountinhibit" => Some (mcountinhibit_ref.(regval_of) (mcountinhibit_ref.(read_from) s))
  | "scounteren" => Some (scounteren_ref.(regval_of) (scounteren_ref.(read_from) s))
  | "mcounteren" => Some (mcounteren_ref.(regval_of) (mcounteren_ref.(read_from) s))
  | "mscratch" => Some (mscratch_ref.(regval_of) (mscratch_ref.(read_from) s))
  | "mtval" => Some (mtval_ref.(regval_of) (mtval_ref.(read_from) s))
  | "mepc" => Some (mepc_ref.(regval_of) (mepc_ref.(read_from) s))
  | "mcause" => Some (mcause_ref.(regval_of) (mcause_ref.(read_from) s))
  | "mtvec" => Some (mtvec_ref.(regval_of) (mtvec_ref.(read_from) s))
  | "medeleg" => Some (medeleg_ref.(regval_of) (medeleg_ref.(read_from) s))
  | "mideleg" => Some (mideleg_ref.(regval_of) (mideleg_ref.(read_from) s))
  | "mie" => Some (mie_ref.(regval_of) (mie_ref.(read_from) s))
  | "mip" => Some (mip_ref.(regval_of) (mip_ref.(read_from) s))
  | "mstatus" => Some (mstatus_ref.(regval_of) (mstatus_ref.(read_from) s))
  | "mstatush" => Some (mstatush_ref.(regval_of) (mstatush_ref.(read_from) s))
  | "misa" => Some (misa_ref.(regval_of) (misa_ref.(read_from) s))
  | "cur_inst" => Some (cur_inst_ref.(regval_of) (cur_inst_ref.(read_from) s))
  | "cur_privilege" => Some (cur_privilege_ref.(regval_of) (cur_privilege_ref.(read_from) s))
  | "x31" => Some (x31_ref.(regval_of) (x31_ref.(read_from) s))
  | "x30" => Some (x30_ref.(regval_of) (x30_ref.(read_from) s))
  | "x29" => Some (x29_ref.(regval_of) (x29_ref.(read_from) s))
  | "x28" => Some (x28_ref.(regval_of) (x28_ref.(read_from) s))
  | "x27" => Some (x27_ref.(regval_of) (x27_ref.(read_from) s))
  | "x26" => Some (x26_ref.(regval_of) (x26_ref.(read_from) s))
  | "x25" => Some (x25_ref.(regval_of) (x25_ref.(read_from) s))
  | "x24" => Some (x24_ref.(regval_of) (x24_ref.(read_from) s))
  | "x23" => Some (x23_ref.(regval_of) (x23_ref.(read_from) s))
  | "x22" => Some (x22_ref.(regval_of) (x22_ref.(read_from) s))
  | "x21" => Some (x21_ref.(regval_of) (x21_ref.(read_from) s))
  | "x20" => Some (x20_ref.(regval_of) (x20_ref.(read_from) s))
  | "x19" => Some (x19_ref.(regval_of) (x19_ref.(read_from) s))
  | "x18" => Some (x18_ref.(regval_of) (x18_ref.(read_from) s))
  | "x17" => Some (x17_ref.(regval_of) (x17_ref.(read_from) s))
  | "x16" => Some (x16_ref.(regval_of) (x16_ref.(read_from) s))
  | "x15" => Some (x15_ref.(regval_of) (x15_ref.(read_from) s))
  | "x14" => Some (x14_ref.(regval_of) (x14_ref.(read_from) s))
  | "x13" => Some (x13_ref.(regval_of) (x13_ref.(read_from) s))
  | "x12" => Some (x12_ref.(regval_of) (x12_ref.(read_from) s))
  | "x11" => Some (x11_ref.(regval_of) (x11_ref.(read_from) s))
  | "x10" => Some (x10_ref.(regval_of) (x10_ref.(read_from) s))
  | "x9" => Some (x9_ref.(regval_of) (x9_ref.(read_from) s))
  | "x8" => Some (x8_ref.(regval_of) (x8_ref.(read_from) s))
  | "x7" => Some (x7_ref.(regval_of) (x7_ref.(read_from) s))
  | "x6" => Some (x6_ref.(regval_of) (x6_ref.(read_from) s))
  | "x5" => Some (x5_ref.(regval_of) (x5_ref.(read_from) s))
  | "x4" => Some (x4_ref.(regval_of) (x4_ref.(read_from) s))
  | "x3" => Some (x3_ref.(regval_of) (x3_ref.(read_from) s))
  | "x2" => Some (x2_ref.(regval_of) (x2_ref.(read_from) s))
  | "x1" => Some (x1_ref.(regval_of) (x1_ref.(read_from) s))
  | "instbits" => Some (instbits_ref.(regval_of) (instbits_ref.(read_from) s))
  | "nextPC" => Some (nextPC_ref.(regval_of) (nextPC_ref.(read_from) s))
  | "PC" => Some (PC_ref.(regval_of) (PC_ref.(read_from) s))
  | _ => None
  end.

Lemma get_regval'_eq r regs:
  get_regval r regs = get_regval' r regs.
Proof.
  unfold get_regval.
  have Hcase : ∀ s e1 e2 (v : option register_value),
      (r = s → e1 = v) →
      (r ≠ s → e2 = v) →
      (if string_dec r s then e1 else e2) = v. {
    move => s ?????. destruct (string_dec r s); eauto.
  }
  repeat (apply Hcase; [move => ->; done| move => ?]).
  unfold get_regval'.
  destruct r => //.
Admitted.
(*
  all: destruct r => //. 1: admit.
  all: destruct r => //.
  1: destruct a0 as [[] [] [] [] [] [] [] []] => //.
  all: destruct r => //.
                    repeat (case_match => //).
*)
*)
Lemma get_set_regval r regs regs' v:
  set_regval r v regs = Some regs' ->
  get_regval r regs' = Some v.
Proof.
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
Admitted.


Lemma get_set_regval_ne r r' regs regs' v:
  set_regval r' v regs = Some regs' →
  r ≠ r' →
  get_regval r regs' = get_regval r regs.
Proof.
  (*
  rewrite !get_regval'_eq.
  unfold get_regval'.
  destruct r => //.
  destruct a as [[] [] [] [] [] [] [] []]; try fast_done.
  all: destruct r => //.
  all: destruct a as [[] [] [] [] [] [] [] []]; try fast_done.
  all: destruct r => //.
  all: try destruct a as [[] [] [] [] [] [] [] []]; try fast_done.

  destruct (decide (r = String 's' ))
                    do 100 try case_match => //.
  - do 100 try case_match => //.
*)
  unfold set_regval, get_regval.
  move => Hset Hneq.
  have Hcase : ∀ s (e1 e2 e1' e2' : option register_value),
      (r = s → e1 = e1') →
      (e2 = e2') →
      (if string_dec r s then e1 else e2) = (if string_dec r s then e1' else e2'). {
    move => s ??????. destruct (string_dec r s); eauto.
  }
  have Hcase2 : ∀ s e1 e2 (P : Prop),
      (r' = s → e1 = Some regs' → P) →
      (e2 = Some regs' → P) →
      (if string_dec r' s then e1 else e2) = Some regs' →
      P. {
    move => s ??????. destruct (string_dec r' s); eauto.
  }
  repeat (apply Hcase; [shelve|]). done.
  Unshelve.
  (* - clear Hcase. move => ?; subst r. simpl. move: Hset. *)
  (*   destruct r'. 1: done. *)
  (*   Set Nested Proofs Allowed. *)
  (*   Lemma string_dec_length A s1 s2 e1 e2: *)
  (*     String.length s1 ≠ String.length s2 → *)
  (*     (if string_dec s1 s2 then e1 else e2) =@{A} e2. *)
  (*   Proof. Admitted. *)
  (*   Create HintDb string_dec_rewrite. *)
  (*   Hint Rewrite string_dec_length using done : string_dec_rewrite. *)
  (*   destruct r'. 1: { autorewrite with string_dec_rewrite. done. } *)
  (*   autorewrite with string_dec_rewrite.  *)
  (*   destruct r'. 1: { autorewrite with string_dec_rewrite. repeat rewrite ->string_dec_length by done. done. } 1: admit. *)
  (*   destruct r' => //. 1: admit. *)
  (*   destruct r' => //. 1: admit. *)
  (*   repeat (apply Hcase2; [shelve|]); done. *)
  (* all: clear Hcase; move => ?; subst r; simpl; move: Hset; repeat (apply Hcase2; [shelve|]); done. *)
Admitted.


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

Lemma length_bitlistFromWord_rev n (w : Word.word n):
  length (bitlistFromWord_rev w) = n.
Proof.
  elim: n w. { move => w. have ->:= Word.shatter_word_0 w. done. }
  move => n IH w. have [b [c ->]]:= Word.shatter_word_S w => /=. by rewrite IH.
Qed.

Lemma bitlistFromWord_rev_lookup_Some n (w : Word.word n) (i : nat) x:
  bitlistFromWord_rev w !! i = Some x ↔ x = Z.testbit (Z.of_N (Word.wordToN w)) i ∧ (i < n)%nat.
Proof.
  revert n w. induction i => /=; intros n w.
  - destruct n => /=.
    + have -> := Word.shatter_word_0 w => /=. naive_solver lia.
    + have [b [? ->]] := Word.shatter_word_S w => /=. rewrite Z.bit0_odd.
      destruct b; rewrite ?N2Z.inj_succ ?Z.odd_succ N2Z.inj_mul ?Z.even_mul ?Z.odd_mul /=.
      all: naive_solver lia.
  - destruct n => /=.
    + have -> := Word.shatter_word_0 w => /=. naive_solver lia.
    + have [b [? ->]] := Word.shatter_word_S w => /=. rewrite IHi.
      have <-: (Z.succ i = S i) by lia. rewrite -Z.div2_bits; [|lia].
      f_equiv; [|lia]. do 2 f_equiv. destruct b; lia.
Qed.

Lemma bitlistFromWord_lookup_Some n (w : Word.word n) (i : nat) x:
  bitlistFromWord w !! i = Some x ↔ x = Z.testbit (Z.of_N (Word.wordToN w)) (n - 1 - i)%nat ∧ (i < n)%nat.
Proof.
  unfold bitlistFromWord. rewrite rev_reverse reverse_lookup_Some bitlistFromWord_rev_lookup_Some ?length_bitlistFromWord_rev.
  naive_solver lia.
Qed.

Lemma wlsb_testbit n (w : Word.word (S n)):
  Word.wlsb w = Z.testbit (Z.of_N (Word.wordToN w)) 0.
Proof.
  have [b [? ->]]:= Word.shatter_word_S w. simpl.
  rewrite Z.bit0_odd. by destruct b; rewrite ?N2Z.inj_succ ?Z.odd_succ N2Z.inj_mul ?Z.even_mul ?Z.odd_mul /=.
Qed.

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
  n ≠ 0%nat →
  getBit w z = Z.testbit (Z.of_N (Word.wordToN w)) (Z.of_nat z).
Proof. destruct n => //=. by rewrite wlsb_testbit wordToN_wrshift' Z.shiftr_spec. Qed.

Lemma wordFromBitlist_rev_spec l (i : nat):
  Z.testbit (Z.of_N (Word.wordToN (wordFromBitlist_rev l))) i = default false (l !! i).
Proof.
  revert l. induction i; intros [|x l] => //=.
  - rewrite Z.bit0_odd. by destruct x; rewrite ?N2Z.inj_succ ?Z.odd_succ N2Z.inj_mul ?Z.even_mul ?Z.odd_mul /=.
  - have <-: (Z.succ i = S i) by lia. rewrite -Z.div2_bits; [|lia].
    rewrite -IHi. f_equal. destruct x; lia.
Qed.

Lemma wordFromBitlist_spec l (i : nat):
  Z.testbit (Z.of_N (Word.wordToN (wordFromBitlist l))) i = default false (rev l !! i).
Proof.
  rewrite /wordFromBitlist. destruct (rev_length l) => /=. rewrite DepEqNat.nat_cast_same.
  by rewrite wordFromBitlist_rev_spec.
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

Lemma length_bitlistFromWord n (w : Word.word n):
  length (bitlistFromWord w) = n.
Proof. by rewrite /bitlistFromWord rev_length length_bitlistFromWord_rev. Qed.

Lemma nat_diff_eq n T l e g (x : T n):
  nat_diff n n l e g x = e x.
Proof. revert T x l e g. induction n => //=. move => T ????. apply (IHn (λ x, T (S x))). Qed.

Lemma fit_bbv_word_id n1 n2 (m : Word.word n1):
  ∀ Heq : n1 = n2, fit_bbv_word m = eq_rect n1 _ m n2 Heq.
Proof. move => Heq. destruct Heq => /=. by rewrite /fit_bbv_word nat_diff_eq. Qed.

Lemma length_bits_of_bytes l:
  (∀ x, x ∈ l → length x = 8%nat) →
  length (bits_of_bytes l) = (length l * 8)%nat.
Proof.
  move => Hf.
  rewrite /bits_of_bytes concat_join map_fmap join_length -list_fmap_compose /compose.
  rewrite (sum_list_fmap 8) // => ?. rewrite /bits_of/= map_fmap fmap_length. apply: Hf.
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
