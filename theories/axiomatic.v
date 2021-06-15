Require Import isla.base isla.opsem.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Relations.Relation_Operators.

Definition thread_id := N.
Definition event_id := N.

Definition bit := bool.

Inductive translation_regime :=
| Translation_regime_EL10 (el2_disabled: bit)
| Translation_regime_EL2
| Translation_regime_EL20
| Translation_regime_EL3.

Inductive translation_stage :=
| Stage_1
| Stage_2.

Inductive translation_level :=
| Translation_level_0
| Translation_level_1
| Translation_level_2
| Translation_level_3
| Translation_level_4.

Inductive exception_level :=
| EL0
| EL1
| EL2
| EL3.

Inductive read_kind :=
| RK_plain
| RK_acquire
| RK_weak_acquire
(* TODO: others *).

Inductive write_kind :=
| WK_plain
| WK_release
(* TODO: others *)
.

Record tlbi_info := {
  (* TODO *)
}.

Record dc_info := {
  (* TODO *)
}.

Inductive barrier_kind :=
| DMB
| DSB
| TLBI (i:tlbi_info)
| DC (i:dc_info).

Definition vmid := bv 16.  (* actually 8 or 16, implementation-defined with FEAT_VMID16 *)

Definition asid := bv 16.

Inductive asid_or_global :=
| AG_asid (asid:asid)
| AG_global.

Record write_address := {
  wa_kind : write_kind;
  wa_input_address : addr;
  wa_physical_address : addr;
  wa_num_bytes : N;
}.

Record write_info := {
  w_kind : write_kind;
  w_input_address : addr;
  w_physical_address : addr;
  w_num_bytes : N;
  w_data: list byte;
  w_tag_value: option bit;  (* an optional capability tag *)
  w_success: bit;
}.

Record read_info := {
  r_kind : read_kind;
  r_input_address : addr;
  r_physical_address : addr;
  r_num_bytes : N;
  r_data: list byte;
  r_tag_value: option bit;  (* an optional capability tag *)
}.

Record translate_info := {
  t_input_address : addr;
  t_intermediate_physical_address : option addr;
  t_physical_address : option addr;
  t_translation_regime : translation_regime;
  t_vmid : vmid;
  t_asid : asid_or_global;
  t_el : exception_level;
  t_stage : translation_stage;
  t_level : translation_level;
  (* TODO: system register values used for the translation *)
  t_invalidated_for_stage_1_2 : bit * bit;
}.

Record fetch_info := {
  f_input_address : addr;
  f_physical_address : addr;
  f_num_bytes : N;
  f_opcode : list byte;  (* to accommodate Armv8-A thumb or RISC-V compressed instructions *)
}.

(** announce branch address `addr`, to induce ctrl dependency *)
Record branch_address_announce_info := {
 ba_input_address : addr;
 ba_physical_address : addr;  (* not sure whether this record should have a PA field *)
}.

(** currently memory barriers, icache&dcache, and TLBIs all here. not sure*)
Record barrier_info := {
 b_kind : barrier_kind;
}.

Inductive memory_action : Set :=
| MA_write_announce (x:write_info)
| MA_write (x:write_info)
| MA_read (x:read_info)
| MA_translate (x:translate_info)
| MA_fetch (x:fetch_info)
| MA_branch_address_announce (x:branch_address_announce_info)
| MA_barrier (x:barrier_info).

(** TODO *)
Definition instruction := unit.

Record event_info := {
  ei_thread_identifier : N;
  ei_label: memory_action;
  ei_inst: instruction;
}.

(*
Inductive memory_action : Type :=
| MA_act (a:trace_label)
  (* TODO: we use these for now, but
  (1) they have to change, e.g. they don't currently have barriers, translate vs. read distinction, faults, etc., and
  (2) the interface between isla-coq and the memory model itself feels wrong
  *)
| MA_fetch (a:addr) (v:valu)
| MA_translate (stg:translation_stage) (hi:addr) (lo:valu).
*)

Definition rel := event_id -> event_id -> Prop.

Record pre_execution := {
  (** number of threads in the pre-execution *)
  pe_threads : N; (* TODO: make the memory model ignore events over that tid *)
  (** labelling function, labelling each event with its memory actions *)
  pe_label : event_id -> event_info; (* TODO: use event_info *)
  (** intra-instruction order: F --iio--> T1 --iio--> T2 --iio--> [R|W] *)
  pe_iio : rel;
  (** fetch program order, the analogue of program-order for `Fetch` events *)
  pe_fpo : rel;
  (** control dependencies *)
  pe_ctrl : rel;
  (** translation data dependencies (correspond to address dependencies) *)
  pe_tdata : rel;
  (** data dependencies *)
  pe_data : rel;
  (* TODO: others??? *)
}.

Definition is_not_target (r : rel) (e : event_id) : Prop :=
  forall e', ~ r e' e.

Definition addr_of_aux (v:valu) : option addr :=
  match v with
  | Val_Bits (BVN 64 x) => Some x
  | _ => None
  end.

Definition addr_of (a:trace_label) : option addr :=
  match a with
  | LReadMem _ _ addr _ _ => addr_of_aux addr
  | LWriteMem _ _  addr _ _ _ => addr_of_aux addr
  | _ => None
  end.

(* TODO: ??? *)
Definition read_kind_of_valu (v : valu) : read_kind :=
  RK_plain.

(* TODO: ??? *)
Definition write_kind_of_valu (v : valu) : write_kind :=
  WK_plain.

Definition tag_value_of_valu_option (vo : valu_option) :=
  match vo with
  | None => None
  | Some x => Some true (* TODO: this is wrong! *)
  end.

Record memory_model := {
  mm_validity : pre_execution -> Prop;
  (* TODO: or should it build execution witnesses explicitly, like Mark Batty's cmm.lem? *)
}.

Definition acyclic (r : rel) : Prop :=
  Irreflexive (clos_trans _ r).

Definition tid_of (pe : pre_execution) (e : event_id) : thread_id :=
  (pe.(pe_label) e).(ei_thread_identifier).

Definition does_not_involve_initial_events (pe : pre_execution) (r : rel) : Prop :=
  (forall e e', r e e' -> tid_of pe e <> 0%N /\ tid_of pe e' <> 0%N)%nat.

Definition either_way (r : rel) (e1 e2 : event_id) : Prop :=
  r e1 e2 \/ r e2 e1.

Definition is_fetch (pe : pre_execution) (e : event_id) : bool :=
  match (pe.(pe_label) e).(ei_label) with
  | MA_fetch _ => true
  | _ => false
  end.

Definition is_translate (pe : pre_execution) (e : event_id) : bool :=
  match (pe.(pe_label) e).(ei_label) with
  | MA_translate _ => true
  | _ => false
  end.

(* TODO: ??? *)
Definition is_explicit_event (pe : pre_execution) (e : event_id) : bool :=
  match (pe.(pe_label) e).(ei_label) with
  | MA_read _ => true
  | MA_write _ => true
  | MA_barrier _ => true
  | MA_fetch _ => false
  | MA_translate _ => false
  | MA_write_announce _ => true (* ??? *)
  | MA_branch_address_announce _ => true (* ??? *)
  end.

Definition wf_fpo (pe : pre_execution) (fpo : rel) : Prop :=
  does_not_involve_initial_events pe fpo /\
  Transitive fpo /\
  Irreflexive fpo /\
  (forall e e', tid_of pe e <> 0%N ->
    is_fetch pe e -> is_fetch pe e' ->
    tid_of pe e = tid_of pe e' -> either_way fpo e e') /\
  (forall e e', fpo e e' -> tid_of pe e = tid_of pe e').

Definition wf_iio (pe : pre_execution) (iio : rel) : Prop :=
  does_not_involve_initial_events pe iio /\
  Transitive iio /\
  Irreflexive iio /\
  (forall e e', iio e e' -> tid_of pe e = tid_of pe e')
  (* TODO: iio is much more complicated than that *)
  .

Definition wf_tdata (pe : pre_execution) (tdata : rel) : Prop :=
  does_not_involve_initial_events pe tdata /\
  (forall e e', tdata e e' -> tid_of pe e = tid_of pe e' /\ is_translate pe e').

Definition wf_pre_execution (pe : pre_execution) : Prop :=
  (forall e, (tid_of pe e <= pe.(pe_threads))%N) /\
  wf_fpo pe pe.(pe_fpo) /\
  wf_iio pe pe.(pe_iio) /\
  wf_tdata pe pe.(pe_tdata) (* TODO: ??? *).

(** `rf` is right-total on reads, and relates a write to a read when the read reads from the write, in which case they are at the same location and of the same value*)
Definition wf_rf (pe : pre_execution) (rf : rel) :=
  does_not_involve_initial_events pe rf /\
  (forall e,
    match (pe.(pe_label) e).(ei_label) with
    | MA_read ri =>
      (exists w, rf w e /\
        match (pe.(pe_label) w).(ei_label) with
        | MA_write wi => ri.(r_physical_address) = wi.(w_physical_address) /\ ri.(r_data) = wi.(w_data)
        | _ => False
        end) /\
      (forall w1 w2, rf w1 e -> rf w2 e -> w1 = w2)
    | _ => ~ (exists e', rf e' e)
    end).

(** `irf` is right-total on fetches, and relates a write to a fetch when the fetch reads from the write, in which case they are at the same location and of the same value*)
Definition wf_irf (pe : pre_execution) (irf : rel) : Prop :=
  does_not_involve_initial_events pe irf /\
  (forall e,
    match (pe.(pe_label) e).(ei_label) with
    | MA_fetch fi =>
      (exists w, irf w e /\
        match (pe.(pe_label) w).(ei_label) with
        | MA_write wi => fi.(f_physical_address) = wi.(w_physical_address) /\ fi.(f_opcode) = wi.(w_data)
        | _ => False
        end) /\
      (forall w1 w2, irf w1 e -> irf w2 e -> w1 = w2)
    | _ => ~ (exists e', irf e' e)
    end).

(** `co` is a per-location-total order over writes *)
Definition wf_co (pe : pre_execution) (co : rel) : Prop :=
  (* initial events are always at the start of `co` *)
  (forall e e', co e e' -> tid_of pe e' <> 0%N) /\
  (* writes at the same location are `co`-related *)
  (forall e e', e <> e' ->
    match (pe.(pe_label) e).(ei_label), (pe.(pe_label) e').(ei_label) with
    | MA_write wi1, MA_write wi2 =>
      wi1.(w_physical_address) = wi2.(w_physical_address) -> co e e' \/ co e' e
    | _, _ => False
    end) /\
  (* and `co` relates only those writes *)
  (forall e e',
     co e e' ->
     match (pe.(pe_label) e).(ei_label), (pe.(pe_label) e').(ei_label) with
     | MA_write wi1, MA_write wi2 => wi1.(w_physical_address) = wi2.(w_physical_address)
     | _, _ => False
     end) /\
  Transitive co /\
  Irreflexive co.

(** Sequential Consistency with Fetches, axiomatically
    This requires translation being turned off. *)
Definition sc : memory_model := {|
  mm_validity := (fun pe =>
  exists co rf irf,
  wf_rf pe rf /\
  wf_irf pe irf /\
  wf_co pe co /\
  let fr := (fun r w => exists w0, rf w0 r /\ co w0 w) in
  let fe := (fun e1 e2 => pe.(pe_iio) e1 e2 /\ is_fetch pe e1 /\ is_explicit_event pe e2) in
  let po := (fun a b => exists fa fb, fe fa a /\ fe fb b /\ pe.(pe_fpo) fa fb) in
  let po_fetch0 := (fun a fb => exists b, po a b /\ fe fb b) in
  let po_fetch := (fun a b => po_fetch0 a b \/ fe a b) in
  acyclic (fun a b => po a b \/ po_fetch a b \/ rf a b \/ fr a b \/ co a b)
  )
|}.

Definition initial_pre_execution_in (pe_initial_state pe : pre_execution) : Prop :=
  (* all events by the initial thread (thread 0) are the same *)
  (forall e,
    tid_of pe e = 0%N ->
    pe_initial_state.(pe_label) e = pe.(pe_label) e) /\
  (* no extraneous edges *)
  ~ (exists e e',
      tid_of pe e = 0%N /\
      (either_way pe.(pe_fpo) e e' \/
      either_way pe.(pe_data) e e' \/
      either_way pe.(pe_ctrl) e e' \/
      either_way pe.(pe_tdata) e e' \/
      either_way pe.(pe_iio) e e')
  ).