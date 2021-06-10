(* a rough sketch of a glueing of the thread-local semantics of isla with an axiomatic memory model *)
(* has fetching, partial page tables (no faults), but no mixed-size, and does not treat system registers properly *)
(* TODO: this really needs proof-reading *)

(* TODO: how to test this given that it produces infinite things, and is very not computing?
Maybe make an "up to n steps" version and prove some relation? *)

(* TODO: there is a design flaw with our encoding of pre-executions that forces having infinitely many initial events  *)

Require Import isla.base isla.opsem.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Require Import Coq.Relations.Relation_Operators.

Definition thread_internal_event_id := nat.
Definition thread_id := nat.
Definition event_id := (thread_id * thread_internal_event_id)%type.

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
  e_thread_identifier : N;
  e_label: memory_action;
  e_inst: instruction;
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
  pe_threads : nat; (* TODO: make the memory model ignore events over that tid *)
  (** labelling function, labelling each event with its memory actions *)
  pe_label : event_id -> memory_action; (* TODO: use event_info *)
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

(** TODO: isla-axiomatic computes this internally; how do we get it? *)
Record dependency_info := {
  depinfo_is_ctrl : bool;
  depinfo_regs_in_data : string -> Prop;
  depinfo_regs_in_addr : string -> Prop;
  depinfo_regs_out : string -> Prop;
}.

(* TODO: not clear how to deal with this *)
Axiom decode : list byte -> (dependency_info * list trc).

(** dependency_reg_map register map, where a register is mapped to the events that it "depends" on *)
Definition dependency_reg_map := gmap string (thread_internal_event_id -> Prop).

(** accumulator to build a pre-execution *)
Record info := mk_info {
  info_tr : trc;
  info_register_dependencies : dependency_reg_map;
  info_registers : reg_map;
  info_current_eid : thread_internal_event_id;
  info_current_fetch : thread_internal_event_id;
  info_fe_srcs : thread_internal_event_id -> Prop;
  info_ctrl_srcs : thread_internal_event_id -> Prop;
  info_data_srcs : thread_internal_event_id -> Prop;
  info_addr_srcs : thread_internal_event_id -> Prop;
  info_iio_srcs : thread_internal_event_id -> Prop;
  info_is_ctrl : bool;
  (* TODO: ???
  info_address_announced : bool;
  *)
}.

Instance eta_info : Settable _ :=
  settable! mk_info <
    info_tr;
    info_register_dependencies;
    info_registers;
    info_current_eid;
    info_current_fetch;
    info_fe_srcs;
    info_ctrl_srcs;
    info_data_srcs;
    info_addr_srcs;
    info_iio_srcs;
    info_is_ctrl
    >.

Definition info_agrees (info1 info2 : info) : Prop :=
  (* TODO: should probably require equal extensions *)
  info1 = info2.

Definition event_deps_of_reg_deps (reg_deps : string -> Prop) (info_regs : dependency_reg_map) (le : thread_internal_event_id) : Prop :=
  exists r s,
    reg_deps r /\
    info_regs !! r = Some s /\
    s le.

Definition update_regs (updated_registers : string -> Prop) (le : thread_internal_event_id) (iregs : dependency_reg_map) (iregs' : dependency_reg_map) : Prop :=
  forall r,
    (updated_registers r ->
      match iregs' !! r with
      | None => False
      | Some s => forall le', s le' <-> le' = le
      end) /\
    (~ updated_registers r ->
      match iregs !! r, iregs' !! r with
      | Some s1, Some s2 => forall r, s1 r <-> s2 r
      | Some _, None => False
      | None, Some _ => False
      | None, None => True
      end).

Definition regs_empty (iregs : dependency_reg_map) : Prop :=
  forall r,
    match iregs !! r with
    | None => True
    | Some s => forall le, ~ s le
    end.

Definition generated_by_local tid (srcs : thread_internal_event_id -> Prop) e (r : rel) : Prop :=
  (forall le', srcs le' -> r (tid, le') e) /\
  (forall e', r e' e -> exists le', srcs le' /\ e' = (tid, le')).

(** TODO: probably need to extend isla-coq? *)
Axiom is_translate : trace_label -> bool.

Definition is_not_target (r : rel) (e : event_id) : Prop :=
  forall e', ~ r e' e.

Definition pre_execution_of_fetch addr tid pe Xnow Xfuture : Prop :=
  let le := Xnow.(info_current_eid) in
  let e := (tid, le) in
  exists v tr' regs',
    pe.(pe_label) e = MA_fetch {| f_input_address := addr; f_physical_address := addr (* TODO: ??? *); f_num_bytes := 4 (* TODO *); f_opcode := v |} /\
    let (depinfo, trs) := decode v in
    List.In tr' trs /\
    update_regs depinfo.(depinfo_regs_out) Xnow.(info_current_eid) Xnow.(info_register_dependencies) regs' /\
    let Xnext := Xnow <| info_tr := tr' |>
      <| info_current_eid := (Xnow.(info_current_eid) + 1)%nat |>
      <| info_current_fetch := le |>
      <| info_fe_srcs := (fun le' => Xnow.(info_fe_srcs) le' \/ le' = le) |>
      <| info_is_ctrl := depinfo.(depinfo_is_ctrl) |>
      <| info_ctrl_srcs := (fun le' => Xnow.(info_ctrl_srcs) le' \/ (depinfo.(depinfo_is_ctrl) /\ le' = le)) |>
      <| info_data_srcs := event_deps_of_reg_deps depinfo.(depinfo_regs_in_data) Xnow.(info_register_dependencies) |>
      <| info_addr_srcs := event_deps_of_reg_deps depinfo.(depinfo_regs_in_addr) Xnow.(info_register_dependencies) |>
      <| info_iio_srcs := (fun le' => le' = le) |>
      <| info_register_dependencies := regs' |> in
    (* iio *)
    is_not_target pe.(pe_iio) e /\
    (* fpo *)
    (forall le', Xnow.(info_fe_srcs) le' -> pe.(pe_fpo) (tid, le') e) /\
    (forall e', pe.(pe_fpo) e' (tid, Xnow.(info_current_eid)) -> exists le', e' = (tid, le') /\ Xnow.(info_fe_srcs) le') /\
    (* ctrl *)
    generated_by_local tid Xnow.(info_ctrl_srcs) e pe.(pe_ctrl) /\
    (* tdata *)
    is_not_target pe.(pe_tdata) e /\
    (* data *)
    is_not_target pe.(pe_data) e (* TODO: is that correct? *) /\
    (* TODO: others? *)
    info_agrees Xnext Xfuture.

Definition replace_addr (a:trace_label) (x:addr) : trace_label :=
  let xx := Val_Bits (BVN 64 x) in
  match a with
  | LReadMem data kind _ len tag => LReadMem data kind xx len tag
  | LWriteMem res kind _ data len tag => LWriteMem res kind xx data len tag
  | _ => a
  end.

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

Definition bit_of_res (x : valu) : bit :=
  true (* TODO *).

Definition action_of_read_or_write (a : trace_label) : memory_action :=
  match a with
  | LReadMem data kind (Val_Bits (BVN 64 addr)) len tag =>
    MA_read {| r_kind := read_kind_of_valu kind;
      r_input_address := addr (* TODO: ??? *);
      r_physical_address := addr;
      r_num_bytes := len;
      r_data := [] (* TODO: ??? *);
      r_tag_value := tag_value_of_valu_option tag |}
  | LWriteMem res kind (Val_Bits (BVN 64 addr)) data len tag =>
    MA_write {| w_kind := write_kind_of_valu kind;
    w_input_address := addr (* TODO: ??? *);
    w_physical_address := addr;
    w_num_bytes := len;
    w_data := [] (* TODO: ??? *);
    w_tag_value := tag_value_of_valu_option tag;
    w_success := bit_of_res res |}
  | _ => MA_barrier {| b_kind := DMB |} (* TODO: this is silly *)
  end.

Definition pre_execution_of_memory_action tid pe a tr' Xnow Xfuture : Prop :=
  match addr_of a with
  | None => False
  | Some addr =>
    let le := Xnow.(info_current_eid) in
    let e := (tid, le) in
    let Xnext :=
      Xnow
      <| info_tr := tr' |>
      <| info_current_eid := (Xnow.(info_current_eid) + 1)%nat |>
      <| info_ctrl_srcs := (fun le' => Xnow.(info_ctrl_srcs) le' \/ (Xnow.(info_is_ctrl) /\ le' = le)) |>
      <| info_iio_srcs := (fun le' => Xnow.(info_iio_srcs) le' \/ if is_translate a then le' = le else False) |> in
    pe.(pe_label) e = action_of_read_or_write a /\
    (* iio *)
    generated_by_local tid Xnow.(info_iio_srcs) e pe.(pe_iio) /\
    (* fpo *)
    is_not_target pe.(pe_fpo) e /\
    (* ctrl *)
    generated_by_local tid Xnow.(info_ctrl_srcs) e pe.(pe_ctrl) /\
    (* tdata *)
    (if is_translate a then generated_by_local tid Xnow.(info_addr_srcs) e pe.(pe_tdata) else is_not_target pe.(pe_tdata) e) /\
    (* data *)
    generated_by_local tid Xnow.(info_data_srcs) e pe.(pe_data) /\
    info_agrees Xnext Xfuture
  end.

(* TODO: this assumes that each instruction generates at most one explicit memory action *)
(* TODO: this uses `nat`s as event IDs, in order. Not convinced this is very usable. Not sure allowing a renumbering is going to be super usable either... *)
Definition pre_execution_of_thread (tid : thread_id) (regs : reg_map) (pe : pre_execution) : Prop :=
  exists (X : nat -> info),
  (X (0%nat)).(info_tr) = [] /\
  regs_empty (X (0%nat)).(info_register_dependencies) /\
  (X (0%nat)).(info_registers) = regs /\
  (forall e, ~ (X (0%nat)).(info_ctrl_srcs) e) /\
  (forall e, ~ (X (0%nat)).(info_fe_srcs) e) /\
  forall (n : nat),
  let Xnow := X n in
  match Xnow.(info_tr) with
  | [] =>
    match next_pc Xnow.(info_registers) (* TODO: does this function do what I think it does? *) with
    | None => False (* TODO: what does this correspond to? *)
    | Some (addr, _) =>
      pre_execution_of_fetch addr tid pe Xnow (X (n+1)%nat)
    end
  | tr =>
    exists ao tr',
      trace_step tr ao tr' ->
      match ao with
      | None =>
        let Xnext := Xnow <| info_tr := tr' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LBranchAddress _) =>
        let Xnext := Xnow <| info_tr := tr' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LReadReg r _ v) =>
        Xnow.(info_registers) !! r = Some v (* TODO: ? *) /\
        let Xnext := Xnow <| info_tr := tr' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LWriteReg r _ v) =>
        let Xnext := Xnow <| info_tr := tr' |>
         <| info_registers := (<[ r := v ]> Xnow.(info_registers)) |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LReadMem _ _ _ _ _ as a | LWriteMem _ _ _ _ _ _ as a) =>
        pre_execution_of_memory_action tid pe a tr' Xnow (X (n+1)%nat)
      | Some (LDone _) => False (* LDone should have an empty trace *)
      | Some (LAssert b) =>
        let Xnext := Xnow <| info_tr := tr' |> in
        b = true /\
        info_agrees Xnext (X (n+1)%nat)
      end
  end
.

Definition pre_execution_of_threads (regss : list reg_map) (pe : pre_execution) : Prop :=
  pe.(pe_threads) = List.length regss /\
  forall (n : nat) regs,
    List.nth_error regss n = Some regs ->
      let tid := (n+1)%nat in (* tid 0 is for the initial state *)
      pre_execution_of_thread tid regs pe.

Record memory_model := {
  mm_validity : pre_execution -> Prop;
  (* TODO: or should it build execution witnesses explicitly, like Mark Batty's cmm.lem? *)
}.

Definition acyclic (r : rel) : Prop :=
  Irreflexive (clos_trans _ r).

Definition does_not_involve_initial_events (pe : pre_execution) (r : rel) : Prop :=
  (forall e e', r e e' -> fst e <> 0 /\ fst e' <> 0)%nat.

(** `rf` is right-total on reads, and relates a write to a read when the read reads from the write, in which case they are at the same location and of the same value*)
Definition wf_rf (pe : pre_execution) (rf : rel) :=
  does_not_involve_initial_events pe rf /\
  (forall e, (fst e <= pe.(pe_threads))%nat ->
    match pe.(pe_label) e with
    | MA_read ri =>
      (exists w, rf w e /\
        match pe.(pe_label) e with
        | MA_write wi => ri.(r_physical_address) = wi.(w_physical_address) /\ ri.(r_data) = wi.(w_data)
        | _ => False
        end) /\
      (forall w1 w2, rf w1 e -> rf w2 e -> w1 = w2)
    | _ => ~ (exists e', rf e' e)
    end).

(** `irf` is right-total on fetches, and relates a write to a fetch when the fetch reads from the write, in which case they are at the same location and of the same value*)
Definition wf_irf (pe : pre_execution) (irf : rel) : Prop :=
  does_not_involve_initial_events pe irf /\
  (forall e, (fst e <= pe.(pe_threads))%nat ->
    match pe.(pe_label) e with
    | MA_fetch fi =>
      (exists w, irf w e /\
        match pe.(pe_label) e with
        | MA_write wi => fi.(f_physical_address) = wi.(w_physical_address) /\ fi.(f_opcode) = wi.(w_data)
        | _ => False
        end) /\
      (forall w1 w2, irf w1 e -> irf w2 e -> w1 = w2)
    | _ => ~ (exists e', irf e' e)
    end).

(** `co` is a per-location-total order over writes *)
Definition wf_co (pe : pre_execution) (co : rel) : Prop :=
  (* initial events are always at the start of `co` *)
  (forall e tid e', co e (tid, e') -> tid <> 0%nat) /\
  (* writes at the same location are `co`-related *)
  (forall e e', (fst e <= pe.(pe_threads))%nat -> (fst e' <= pe.(pe_threads))%nat -> e <> e' ->
    match pe.(pe_label) e, pe.(pe_label) e' with
    | MA_write wi1, MA_write wi2 =>
      wi1.(w_physical_address) = wi2.(w_physical_address) -> co e e' \/ co e' e
    | _, _ => False
    end) /\
  (* and `co` relates only those writes *)
  (forall e e',
     co e e' ->
     match pe.(pe_label) e, pe.(pe_label) e' with
     | MA_write wi1, MA_write wi2 => wi1.(w_physical_address) = wi2.(w_physical_address)
     | _, _ => False
     end) /\
  Transitive co /\
  Irreflexive co.

Definition is_fetch (pe : pre_execution) (e : event_id) : bool :=
  match pe.(pe_label) e with
  | MA_fetch _ => true
  | _ => false
  end.

(* TODO: ??? *)
Definition is_explicit_event (pe : pre_execution) (e : event_id) : bool :=
  match pe.(pe_label) e with
  | MA_read _ => true
  | MA_write _ => true
  | MA_barrier _ => true
  | MA_fetch _ => false
  | MA_translate _ => false
  | MA_write_announce _ => true (* ??? *)
  | MA_branch_address_announce _ => true (* ??? *)
  end.

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

Definition either_way (r : rel) (e1 e2 : event_id) : Prop :=
  r e1 e2 \/ r e2 e1.

Definition initial_pre_execution_in (pe_initial_state pe : pre_execution) : Prop :=
  (* all events by the initial thread (thread 0) are the same *)
  (forall le,
    let e := (0%nat, le) in
    pe_initial_state.(pe_label) e = pe.(pe_label) e) /\
  (* no extraneous edges *)
  ~ (exists le e',
      let e := (0%nat, le) in
      either_way pe.(pe_fpo) e e' \/
      either_way pe.(pe_data) e e' \/
      either_way pe.(pe_ctrl) e e' \/
      either_way pe.(pe_tdata) e e' \/
      either_way pe.(pe_iio) e e'
  ).

(** Top-level definition of the semantics of running a machine from a starting state `regss` *)
Definition valid_execution_of (regss : list reg_map) (pe_initial_state : pre_execution) (pe : pre_execution) (mm : memory_model) : Prop :=
  initial_pre_execution_in pe_initial_state pe /\
  pre_execution_of_threads regss pe /\
  mm.(mm_validity) pe.