(* a rough sketch of a glueing of the thread-local semantics of isla with an axiomatic memory model *)
(* has fetching, but no mixed-size, no page tables, and does not treat system registers properly *)

(* TODO: how to test this given that it produces infinite things, and is very not computing?
Maybe make an "up to n steps" version and prove some relation? *)

(* TODO: there is a bug with our encoding that forces having infinitely many initial events  *)

Require Import isla.base.
Require Import isla.opsem.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition thread_internal_event_id := nat.
Definition thread_id := nat.
Definition event_id := (thread_id * thread_internal_event_id)%type.

Inductive memory_action :=
| Act (a:trace_label) (* TODO: we use these for now, but (1) they have to change, e.g. they don't currently have barriers, and (2) the interface between isla-coq and the memory model itself has to change, e.g. for `data` vs. `addr` *)
| Fetch (a:addr) (v:valu).

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
  (* data dependencies `[[r = R x; W y r]] = { R x v --data--> W y v | v \in Val } *)
  pe_data : event_id -> event_id -> Prop;
  (* TODO: address dependencies
  pe_addr : event_id -> event_id -> Prop; *)
  (* control dependencies *)
  pe_ctrl : event_id -> event_id -> Prop;
}.

(* TODO: not clear how to deal with this *)
Axiom decode : valu -> list trc.

(** instrumented register map, where a register is mapped to the pair of a value and a set of events that it data-depends on *)
Definition instrumented_reg_map := gmap string (valu * list thread_internal_event_id).

(** agreement on values between an instrumented register map and a (plain) register map *)
Definition agree_regs (iregs : instrumented_reg_map) (regs : reg_map) : Prop :=
  forall (r : string),
    match regs !! r with
    | None =>
      match iregs !! r with
      | Some _ => False
      | None => True
      end
    | Some v =>
      match iregs !! r with
      | Some (v', []) => v = v'
      | _ => False
      end
    end.

(** accumulator to build a pre-execution *)
Record info := mk_info {
  info_tr : trc;
  info_regs : instrumented_reg_map;
  info_cur_eid : thread_internal_event_id;
  info_fe_src : thread_internal_event_id;
  info_ctrl_srcs : thread_internal_event_id -> Prop;
  info_data_srcs : thread_internal_event_id -> Prop;
  (* TODO:
  info_address_announced : bool;
  info_addr_srcs : thread_internal_event_id -> Prop;
  *)
  (* TODO: iio? *)
}.

Instance eta_info : Settable _ :=
  settable! mk_info <info_tr; info_regs; info_cur_eid; info_fe_src; info_ctrl_srcs; info_data_srcs>.

Definition info_agrees (info1 info2 : info) : Prop :=
  info1 = info2. (* TODO: should probably require equal extensions *)

(* TODO: how to separate addr from data? if we have an ``announce address'' event, then it's easy *)
(* TODO: this assumes that each instruction generates at most one explicit memory action *)
(* TODO: this uses `nat`s as event IDs, in order. Not convinced this is very usable... *)
(* TODO: this assumes that LBranchAddress exactly characterises how `ctrl` edges are generated - is that true? *)
Definition pre_execution_of_thread (tid : thread_id) (regs : reg_map) (pe : pre_execution) : Prop :=
  exists (X : nat -> info),
  (X (0%nat)).(info_tr) = [] /\
  (forall e, ~ (X (0%nat)).(info_ctrl_srcs) e) /\
  agree_regs (X (0%nat)).(info_regs) regs /\
  forall (n : nat),
  let Xnow := X n in
  match Xnow.(info_tr) with
  | [] =>
    match next_pc regs (* TODO: does this function do what I think it does? *) with
    | None => False (* TODO: what does this correspond to? *)
    | Some (addr, _) =>
      let e := (tid, Xnow.(info_cur_eid)) in
      exists v tr',
        pe.(pe_label) e = Fetch addr v /\
        List.In tr' (decode v) /\
        let Xnext := Xnow <| info_tr := tr' |>
          <| info_cur_eid := (Xnow.(info_cur_eid) + 1)%nat |>
          <| info_fe_src := Xnow.(info_cur_eid) |>
          <| info_data_srcs := (fun _ => False) |> in
        (n > 0 -> pe.(pe_fpo1) (tid, (X (n-1)%nat).(info_fe_src)) e) /\
        (forall e', pe.(pe_fpo1) e' (tid, Xnow.(info_cur_eid)) -> e' = (tid, (X (n-1)%nat).(info_fe_src) )) /\
        (~ (exists e', pe.(pe_ctrl) e' e)) /\
        info_agrees Xnext (X (n+1)%nat)
    end
  | tr =>
    exists ao tr',
      trace_step tr ao tr' ->
      match ao with
      | None =>
        let Xnext := Xnow <| info_tr := tr' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LBranchAddress _) =>
        let Xnext := Xnow <| info_ctrl_srcs := (fun e' => Xnow.(info_data_srcs) e' \/ Xnow.(info_ctrl_srcs) e') |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LReadReg r _ v) =>
        exists s, Xnow.(info_regs) !! r = Some s /\ v = fst s /\
        (* TODO: is this the right event? *)
        let Xnext := Xnow <| info_data_srcs := (fun e' => (List.In e' (snd s)) \/ Xnow.(info_data_srcs) e') |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LWriteReg r _ v) =>
        let e := (tid, Xnow.(info_cur_eid)) in
        let info_regs' := <[ r := (v, [Xnow.(info_cur_eid)]) ]> Xnow.(info_regs) in
        let Xnext := Xnow <| info_regs := info_regs' |> in
        info_agrees Xnext (X (n+1)%nat)
      | Some (LReadMem _ _ _ _ _ as a | LWriteMem _ _ _ _ _ _ as a) =>
        let e := (tid, Xnow.(info_cur_eid)) in
        pe.(pe_label) e = Act a /\
        let Xnext := Xnow <| info_tr := tr' |>
          <| info_cur_eid := (Xnow.(info_cur_eid) + 1)%nat |> in
        pe.(pe_fe) (tid, Xnow.(info_fe_src)) e /\
        (forall e', pe.(pe_fe) e' e -> e' = (tid, Xnow.(info_fe_src) )) /\
        (forall e', Xnow.(info_ctrl_srcs) e' -> pe.(pe_ctrl) (tid, e') e) /\
        (forall e', pe.(pe_ctrl) e' e -> exists le', Xnow.(info_ctrl_srcs) le' /\ e' = (tid, le')) /\
        (forall e', Xnow.(info_data_srcs) e' -> (tid, e') <> e -> pe.(pe_data) (tid, e') e) /\
        (forall e', pe.(pe_data) e' e -> exists le', Xnow.(info_data_srcs) le' /\ e' = (tid, le') /\ e' <> e) /\
        info_agrees Xnext (X (n+1)%nat)
      | Some (LDone _) => False (* TODO: right? *)
      | Some (LAssert b) => b = true /\ info_agrees Xnow (X (n+1)%nat)
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

(*** Sequential Consistency with Fetches, axiomatically *)
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

Definition initial_pre_execution_in (pe_initial_state pe : pre_execution) : Prop :=
  (* all events by the initial thread (thread 0) are the same *)
  (forall le,
    let e := (0%nat, le) in
    pe_initial_state.(pe_label) e = pe.(pe_label) e) /\
  (* no extraneous edges *)
  ~ (exists le e',
      let e := (0%nat, le) in
      pe.(pe_fe) e e' \/ pe.(pe_fe) e' e \/
      pe.(pe_fpo1) e e' \/ pe.(pe_fpo1) e' e \/
      pe.(pe_data) e e' \/ pe.(pe_data) e' e \/
      pe.(pe_ctrl) e e' \/ pe.(pe_ctrl) e' e
  ).

Definition valid_execution_of (regss : list reg_map) (pe_initial_state : pre_execution) (pe : pre_execution) (mm : memory_model) : Prop :=
  initial_pre_execution_in pe_initial_state pe /\
  pre_execution_of_threads regss pe /\
  mm.(mm_validity) pe.