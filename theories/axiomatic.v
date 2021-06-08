(* a rough sketch of a glueing of the thread-local semantics of isla with an axiomatic memory model *)
(* has fetching, but no mixed-size, no page tables, and does not treat system registers properly *)
(* TODO: this really needs proof-reading *)

(* TODO: how to test this given that it produces infinite things, and is very not computing?
Maybe make an "up to n steps" version and prove some relation? *)

(* TODO: there is a design flaw with our encoding of pre-executions that forces having infinitely many initial events  *)

Require Import isla.base.
Require Import isla.opsem.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition thread_internal_event_id := nat.
Definition thread_id := nat.
Definition event_id := (thread_id * thread_internal_event_id)%type.

Inductive memory_action :=
| Act (a:trace_label)
  (* TODO: we use these for now, but
  (1) they have to change, e.g. they don't currently have barriers, and
  (2) the interface between isla-coq and the memory model itself feels wrong
  *)
| Fetch (a:addr) (v:valu)
| Translate1 (va:addr) (ipa:addr)
| Translate2 (ipa:addr) (pa:addr).

Record pre_execution := {
  (* The number of threads in the pre-execution *)
  pe_threads : nat; (* TODO: make the memory model ignore events over that tid *)
  (* the labelling function, labelling each event with its memory actions *)
  pe_label : event_id -> memory_action; (* TODO: or option? *)
  (* The fetch-to-execute order relates a fetch to the event it fetches for:
    F x v --fe--> R x v', where decode(v) = R x
  *)
  pe_fe : event_id -> event_id -> Prop;
  (* The transitive reduction (because it's easier to compute) of `fpo`, the analogue pf program-order for `Fetch` events
  Instead of a primitive `po` between `b` and `d`, we have
    a:F x1 v1 -------> b:A1
       |               .
       | fpo           . po as a derived edge
       |               .
       v               v
    c:F x2 v2 -------> d:A2
  *)
  pe_fpo1 : event_id -> event_id -> Prop;
  (* data dependencies.
    `r = R x; W y r` leads to
       R x v --data--> W y v
  *)
  pe_data : event_id -> event_id -> Prop;
  (* address dependencies *)
  pe_addr : event_id -> event_id -> Prop;
  (* translation data dependencies (correspond to address dependencies) *)
  pe_tdata : event_id -> event_id -> Prop;
  (* control dependencies *)
  pe_ctrl : event_id -> event_id -> Prop;
  (* intra-instruction ordering: T1 --iio--> T2 --iio--> W *)
  pe_iio : event_id -> event_id -> Prop;
}.

(** TODO: *)
Record dependency_info := {
  depinfo_is_ctrl : bool;
  depinfo_regs_in_data : string -> Prop;
  depinfo_regs_in_addr : string -> Prop;
  depinfo_regs_out : string -> Prop;
}.

(* TODO: not clear how to deal with this *)
Axiom decode : valu -> (dependency_info * list trc).

(** instrumented register map, where a register is mapped to the events that it "depends" on *)
Definition instrumented_reg_map := gmap string (thread_internal_event_id -> Prop).

Inductive translation_level : Type :=
(* TODO: it's probably more complicated *)
| Trlvl_plain_address
| Trlvl_translation_off
| Trlvl_stage_one_only (** VA to IPA *)
| Trlvl_stage_one_and_two (** VA to IPA + IPA to PA *).

(** accumulator to build a pre-execution *)
Record info := mk_info {
  info_tr : trc;
  info_regs : instrumented_reg_map;
  info_regs2 : reg_map;
  info_cur_eid : thread_internal_event_id;
  info_fe_src : thread_internal_event_id;
  info_ctrl_srcs : thread_internal_event_id -> Prop;
  info_data_srcs : thread_internal_event_id -> Prop;
  info_addr_srcs : thread_internal_event_id -> Prop;
  info_translation_level : translation_level;
  (* TODO:
  info_address_announced : bool;
  *)
  (* TODO: iio? *)
}.

Instance eta_info : Settable _ :=
  settable! mk_info <info_tr;
    info_regs;
    info_regs2;
    info_cur_eid;
    info_fe_src;
    info_ctrl_srcs;
    info_data_srcs;
    info_addr_srcs;
    info_translation_level>.

Definition info_agrees (info1 info2 : info) : Prop :=
  info1 = info2. (* TODO: should probably require equal extensions *)

Definition event_deps_of_reg_deps (reg_deps : string -> Prop) (info_regs : instrumented_reg_map) (le : thread_internal_event_id) : Prop :=
  exists r s,
    reg_deps r /\
    info_regs !! r = Some s /\
    s le.

Definition update_regs (updated_registers : string -> Prop) (le : thread_internal_event_id) (iregs : instrumented_reg_map) (iregs' : instrumented_reg_map) : Prop :=
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

Definition regs_empty (iregs : instrumented_reg_map) : Prop :=
  forall r,
    match iregs !! r with
    | None => True
    | Some s => forall le, ~ s le
    end.

Definition pre_execution_of_fetch is_initial addr tid pe Xnow Xfuture : Prop :=
  let e := (tid, Xnow.(info_cur_eid)) in
  exists v tr' regs',
    pe.(pe_label) e = Fetch addr v /\
    let (depinfo, trs) := decode v in
    List.In tr' trs /\
    update_regs depinfo.(depinfo_regs_out) Xnow.(info_cur_eid) Xnow.(info_regs) regs' /\
    let Xnext := Xnow <| info_tr := tr' |>
      <| info_cur_eid := (Xnow.(info_cur_eid) + 1)%nat |>
      <| info_fe_src := Xnow.(info_cur_eid) |>
      <| info_ctrl_srcs := (fun le => Xnow.(info_ctrl_srcs) le \/ (depinfo.(depinfo_is_ctrl) /\ le = Xnow.(info_cur_eid))) |>
      <| info_data_srcs := event_deps_of_reg_deps depinfo.(depinfo_regs_in_data) Xnow.(info_regs) |>
      <| info_addr_srcs := event_deps_of_reg_deps depinfo.(depinfo_regs_in_addr) Xnow.(info_regs) |>
      <| info_regs := regs' |> in
    (~ is_initial -> pe.(pe_fpo1) (tid, Xnow.(info_fe_src)) e) /\
    (forall e', pe.(pe_fpo1) e' (tid, Xnow.(info_cur_eid)) -> e' = (tid, Xnow.(info_fe_src) )) /\
    (~ (exists e', pe.(pe_ctrl) e' e)) /\
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

Definition pre_execution_of_memory_action tid pe a tr' Xnow Xfuture : Prop :=
  match addr_of a with
  | None => False
  | Some addr =>
  let k := (match Xnow.(info_translation_level) with | Trlvl_plain_address => 0 | Trlvl_translation_off => 0 | Trlvl_stage_one_only => 1 | Trlvl_stage_one_and_two => 2 end)%nat in
  let e := (tid, Xnow.(info_cur_eid) + k)%nat in
  (match Xnow.(info_translation_level) with
  | Trlvl_plain_address =>
    pe.(pe_label) e = Act a /\
    (forall e', Xnow.(info_addr_srcs) e' -> (tid, e') <> e -> pe.(pe_addr) (tid, e') e) /\
    (* addr *)
    (forall e', Xnow.(info_addr_srcs) e' -> (tid, e') <> e -> pe.(pe_addr) (tid, e') e) /\
    (forall e', pe.(pe_addr) e' e -> exists le', Xnow.(info_addr_srcs) le' /\ e' = (tid, le') /\ e' <> e) /\
    (* tdata *)
    (forall e', ~ pe.(pe_tdata) e' e) /\
    (* iio *)
    (forall e', ~ pe.(pe_iio) e' e) /\
    (* TODO: ??? *)
    True
  | Trlvl_translation_off =>
    pe.(pe_label) e = Act a /\
    (forall e', Xnow.(info_addr_srcs) e' -> (tid, e') <> e -> pe.(pe_addr) (tid, e') e) /\
    (* addr *)
    (forall e', ~ pe.(pe_addr) e' e) /\
    (* tdata *)
    (forall e', ~ pe.(pe_tdata) e' e) /\
    (* iio *)
    (forall e', ~ pe.(pe_iio) e' e) /\
    (* TODO: ??? *)
    True
  | Trlvl_stage_one_only =>
    let etr := (tid, Xnow.(info_cur_eid)) in
    exists ipa,
    pe.(pe_label) e = Act (replace_addr a ipa) /\
    pe.(pe_label) etr = Translate1 addr ipa /\
    (* addr *)
    (forall e', ~ pe.(pe_addr) e' e) /\
    (forall e', ~ pe.(pe_addr) e' etr) /\
    (* tdata *)
    (forall e', Xnow.(info_addr_srcs) e' -> (tid, e') <> etr -> pe.(pe_tdata) (tid, e') e) /\
    (forall e', pe.(pe_tdata) e' etr -> exists le', Xnow.(info_addr_srcs) le' /\ e' = (tid, le') /\ e' <> etr) /\
    (forall e', ~ pe.(pe_tdata) e' e) /\
    (* iio *)
    (forall e', ~ pe.(pe_iio) e' etr) /\
    (pe.(pe_iio) etr e) /\
    (forall e', pe.(pe_iio) e' e -> e' = etr) /\
    True (* TODO *)
  | Trlvl_stage_one_and_two =>
    let etr1 := (tid, Xnow.(info_cur_eid)) in
    let etr2 := (tid, Xnow.(info_cur_eid) + 1)%nat in
    exists ipa pa,
    pe.(pe_label) e = Act (replace_addr a pa) /\
    pe.(pe_label) etr1 = Translate1 addr ipa /\
    pe.(pe_label) etr2 = Translate2 ipa pa /\
    (* addr *)
    (forall e', ~ pe.(pe_addr) e' e) /\
    (forall e', ~ pe.(pe_addr) e' etr1) /\
    (forall e', ~ pe.(pe_addr) e' etr2) /\
    (* tdata *)
    (forall e', Xnow.(info_addr_srcs) e' -> (tid, e') <> etr1 -> pe.(pe_tdata) (tid, e') e) /\
    (forall e', pe.(pe_tdata) e' etr1 -> exists le', Xnow.(info_addr_srcs) le' /\ e' = (tid, le') /\ e' <> etr1) /\
    (forall e', ~ pe.(pe_tdata) e' etr2) /\
    (forall e', ~ pe.(pe_tdata) e' e) /\
    (* iio *)
    (forall e', ~ pe.(pe_iio) e' etr1) /\
    (pe.(pe_iio) etr1 etr2) /\
    (pe.(pe_iio) etr2 e) /\
    (pe.(pe_iio) etr1 e) /\
    (forall e', pe.(pe_iio) e' e -> e' = etr1 \/ e' = etr2) /\
    (forall e', pe.(pe_iio) e' etr2 -> e' = etr1) /\
    True (* TODO *)
  end) /\
  let Xnext := Xnow <| info_tr := tr' |>
    <| info_cur_eid := (Xnow.(info_cur_eid) + 1 + k)%nat |> in
  (* fe *)
  pe.(pe_fe) (tid, Xnow.(info_fe_src)) e /\
  (forall e', pe.(pe_fe) e' e -> e' = (tid, Xnow.(info_fe_src) )) /\
  (* ctrl *)
  (forall e', Xnow.(info_ctrl_srcs) e' -> (tid, e') <> e -> pe.(pe_ctrl) (tid, e') e) /\
  (forall e', pe.(pe_ctrl) e' e -> e' <> e /\ exists le', Xnow.(info_ctrl_srcs) le' /\ e' = (tid, le')) /\
  (* data *)
  (forall e', Xnow.(info_data_srcs) e' -> (tid, e') <> e -> pe.(pe_data) (tid, e') e) /\
  (forall e', pe.(pe_data) e' e -> exists le', Xnow.(info_data_srcs) le' /\ e' = (tid, le') /\ e' <> e) /\
  info_agrees Xnext Xfuture
  end.

Record thread_state := {
  ts_regs: reg_map;
  ts_translation_level : translation_level;
}.

(* TODO: this assumes that each instruction generates at most one explicit memory action *)
(* TODO: this uses `nat`s as event IDs, in order. Not convinced this is very usable. Not sure allowing a renumbering is going to be super usable either... *)
Definition pre_execution_of_thread (tid : thread_id) (regs : thread_state) (pe : pre_execution) : Prop :=
  exists (X : nat -> info),
  (X (0%nat)).(info_tr) = [] /\
  regs_empty (X (0%nat)).(info_regs) /\
  (X (0%nat)).(info_regs2) = regs.(ts_regs) /\
  (X (0%nat)).(info_translation_level) = regs.(ts_translation_level) /\
  (forall e, ~ (X (0%nat)).(info_ctrl_srcs) e) /\
  forall (n : nat),
  let Xnow := X n in
  match Xnow.(info_tr) with
  | [] =>
    match next_pc Xnow.(info_regs2) (* TODO: does this function do what I think it does? *) with
    | None => False (* TODO: what does this correspond to? *)
    | Some (addr, _) =>
      pre_execution_of_fetch (n > 0) addr tid pe Xnow (X (n+1)%nat)
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
        Xnow.(info_regs2) !! r = Some v (* TODO: ? *) /\
        let Xnext := Xnow <| info_tr := tr' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LWriteReg r _ v) =>
        let Xnext := Xnow <| info_tr := tr' |>
         <| info_regs2 := (<[ r := v ]> Xnow.(info_regs2)) |> in
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

Definition pre_execution_of_threads (regss : list thread_state) (pe : pre_execution) : Prop :=
  pe.(pe_threads) = List.length regss /\
  forall (n : nat) regs,
    List.nth_error regss n = Some regs ->
      let tid := (n+1)%nat in (* tid 0 is for the initial state *)
      pre_execution_of_thread tid regs pe.

Record memory_model := {
  mm_validity : pre_execution -> Prop;
  (* TODO: or should it build execution witnesses explicitly, like Mark Batty's cmm.lem? *)
}.

Require Import Coq.Relations.Relation_Operators.

Definition acyclic (r : event_id -> event_id -> Prop) : Prop :=
  Irreflexive (clos_trans _ r).

Definition does_not_involve_initial_events (pe : pre_execution) (R : event_id -> event_id -> Prop) : Prop :=
  (forall e e', R e e' -> fst e <> 0 /\ fst e' <> 0)%nat.

(** `rf` is right-total on reads, and relates a write to a read when the read reads from the write, in which case they are at the same location and of the same value*)
Definition wf_rf (pe : pre_execution) (rf : event_id -> event_id -> Prop) :=
  does_not_involve_initial_events pe rf /\
  (forall e, (fst e <= pe.(pe_threads))%nat ->
    match pe.(pe_label) e with
    | Act (LReadMem v _ addr _ _) =>
      (exists w, rf w e /\
        match pe.(pe_label) e with
        | Act (LWriteMem _ _ addr' v' _ _) => addr = addr' /\ v = v'
        | _ => False
        end) /\
      (forall w1 w2, rf w1 e -> rf w2 e -> w1 = w2)
    | _ => ~ (exists e', rf e' e)
    end).

(** `irf` is right-total on fetches, and relates a write to a fetch when the fetch reads from the write, in which case they are at the same location and of the same value*)
Definition wf_irf (pe : pre_execution) (irf : event_id -> event_id -> Prop) : Prop :=
  does_not_involve_initial_events pe irf /\
  (forall e, (fst e <= pe.(pe_threads))%nat ->
    match pe.(pe_label) e with
    | Fetch addr v =>
      (exists w, irf w e /\
        match pe.(pe_label) e with
        | Act (LWriteMem _ _ addr' v' _ _) => addr' = Val_Bits (BVN 64 addr) /\ v = v'
        | _ => False
        end) /\
      (forall w1 w2, irf w1 e -> irf w2 e -> w1 = w2)
    | _ => ~ (exists e', irf e' e)
    end).

(** `co` is a per-location-total order over writes *)
Definition wf_co (pe : pre_execution) (co : event_id -> event_id -> Prop) : Prop :=
  (* initial events are always at the start of `co` *)
  (forall e tid e', co e (tid, e') -> tid <> 0%nat) /\
  (* writes at the same location are `co`-related *)
  (forall e e', (fst e <= pe.(pe_threads))%nat -> (fst e' <= pe.(pe_threads))%nat -> e <> e' ->
    match pe.(pe_label) e, pe.(pe_label) e' with
    | Act (LWriteMem _ _ addr1 _ _ _), Act (LWriteMem _ _ addr2 _ _ _) =>
      addr1 = addr2 -> co e e' \/ co e' e
    | _, _ => False
    end) /\
  (* and `co` relates only those writes *)
  (forall e e',
     co e e' ->
     match pe.(pe_label) e, pe.(pe_label) e' with
     | Act (LWriteMem _ _ addr1 _ _ _), Act (LWriteMem _ _ addr2 _ _ _) => addr1 = addr2
     | _, _ => False
     end) /\
  Transitive co /\
  Irreflexive co.

(*** Sequential Consistency with Fetches, axiomatically
     This requires translation being turned off. *)
Definition sc : memory_model := {|
  mm_validity := (fun pe =>
  exists co rf irf,
  wf_rf pe rf /\
  wf_irf pe irf /\
  wf_co pe co /\
  let fr := (fun r w => exists w0, rf w0 r /\ co w0 w) in
  let fpo := (fun a b => clos_trans _ pe.(pe_fpo1) a b) in
  let po := (fun a b => exists fa fb, pe.(pe_fe) fa a /\ pe.(pe_fe) fb b /\ fpo fa fb) in
  let po_fetch0 := (fun a fb => exists b, po a b /\ pe.(pe_fe) fb b) in
  let po_fetch := (fun a b => po_fetch0 a b \/ pe.(pe_fe) a b) in
  acyclic (fun a b => po a b \/ po_fetch a b \/ rf a b \/ fr a b \/ co a b)
  )
|}.

Definition either_way (r : event_id -> event_id -> Prop) (e1 e2 : event_id) : Prop :=
  r e1 e2 \/ r e2 e1.

Definition initial_pre_execution_in (pe_initial_state pe : pre_execution) : Prop :=
  (* all events by the initial thread (thread 0) are the same *)
  (forall le,
    let e := (0%nat, le) in
    pe_initial_state.(pe_label) e = pe.(pe_label) e) /\
  (* no extraneous edges *)
  ~ (exists le e',
      let e := (0%nat, le) in
      either_way pe.(pe_fe) e e' \/
      either_way pe.(pe_fpo1) e e' \/
      either_way pe.(pe_data) e e' \/
      either_way pe.(pe_ctrl) e e' \/
      either_way pe.(pe_addr) e e' \/
      either_way pe.(pe_tdata) e e' \/
      either_way pe.(pe_iio) e e'
  ).

(* TODO: need a way to specify `info` more, like translation level, etc. *)
Definition valid_execution_of (regss : list thread_state) (pe_initial_state : pre_execution) (pe : pre_execution) (mm : memory_model) : Prop :=
  initial_pre_execution_in pe_initial_state pe /\
  pre_execution_of_threads regss pe /\
  mm.(mm_validity) pe.