Require Export Sail.Base.
Require Export Sail.Prompt_monad.
Require Export RV64.riscv_types.
Require Export RV64.mem_metadata.
Require Export RV64.riscv_extras.
Require Export RV64.riscv.

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

Lemma x10_nextPC regs n:
  (x10 {[ regs with nextPC := n ]} ) = x10 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma x11_nextPC regs n:
  (x11 {[ regs with nextPC := n ]} ) = x11 regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma PC_nextPC regs n:
  (PC {[ regs with nextPC := n ]} ) = PC regs.
Proof. now rewrite (regstate_eta regs). Qed.
Lemma nextPC_nextPC regs n:
  (nextPC {[ regs with nextPC := n ]} ) = n.
Proof. now rewrite (regstate_eta regs). Qed.

(* This breaks the `with` notations so we have to import it later. *)
Require Import refinedc.lithium.base.

(* This file should not depend on anything in isla-coq since it is quite slow to compile. *)

Lemma get_word_word_binop {n} f (b1 b2 : mword n):
  get_word (word_binop f b1 b2) = f _ (get_word b1) (get_word b2).
Proof. by destruct n. Qed.

Lemma get_word_to_word n H (w : Word.word (Z.to_nat n)):
  get_word (to_word H w) = w.
Proof. destruct n => //. Qed.

Lemma lt_Npow2 n n1:
  (0 ≤ n1)%Z →
  (n < NatLib.Npow2 (Z.to_nat n1))%N ↔ (Z.of_N n < 2 ^ n1)%Z.
Proof.
  move => ?.
  rewrite -Npow2_pow Z_nat_N. etrans; [ apply N2Z.inj_lt |].
  by rewrite N2Z.inj_pow Z2N.id.
Qed.

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
  (* all: clear Hcase; move => ?; subst r; simpl; move: Hset; repeat (apply Hcase2; [shelve|]); done. *)
Admitted.

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
