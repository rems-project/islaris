(* a rough sketch of a glueing of the thread-local semantics of isla with an axiomatic memory model *)
(* has fetching, but no mixed-size, no page tables *)

(* TODO: how to test this given that it produces infinite things, and is very not computing?
Maybe make an "up to n steps" version and prove some relation? *)

Require Import isla.base.
Require Import isla.opsem.

From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

Definition thread_internal_event_id := nat.
Definition thread_id := nat.
Definition event_id := (thread_id * thread_internal_event_id)%type.

Inductive memory_action :=
| Act (a:trace_label)
| Fetch (a:addr) (v:valu). (* TODO: for now... *)

Record pre_execution := {
  pe_threads : nat; (* TODO: make the memory model ignore events over that tid *)
  pe_lab : event_id -> memory_action; (* or option? *)
  pe_fe : event_id -> event_id -> Prop;
  pe_fpo1 : event_id -> event_id -> Prop;
  pe_data : event_id -> event_id -> Prop;
  pe_ctrl : event_id -> event_id -> Prop;
}.

Axiom decode : valu -> list trc.

Definition instr_reg_map := gmap string (valu * list thread_internal_event_id).

Definition agree_regs (iregs : instr_reg_map) (regs : reg_map) : Prop :=
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

Record info := mk_info {
  info_tr : trc;
  info_cur_eid : thread_internal_event_id;
  info_fe_src : thread_internal_event_id;
  info_ctrl_srcs : thread_internal_event_id -> Prop;
  info_regs : instr_reg_map;
  info_data_srcs : thread_internal_event_id -> Prop;
  (* TODO: iio? *)
}.

Instance eta_info : Settable _ :=
  settable! mk_info <info_tr; info_cur_eid; info_fe_src; info_ctrl_srcs; info_regs; info_data_srcs>.

Definition info_agrees (info1 info2 : info) : Prop :=
  info1 = info2. (* TODO: should probably require equal extensions *)

Definition my_insert (r : string) v (iregs : instr_reg_map) :=
  <[ r := v ]> iregs.

(* TODO: data, ctrl, ...; but how to separate addr from data? *)
(* TODO: this assumes that each instruction generates at most one explicit memory action *)
Definition pre_execution_of_thread (tid : thread_id) (regs : reg_map) (pe : pre_execution) : Prop :=
  exists (X : nat -> info),
  (X (0%nat)).(info_tr) = [] /\
  (forall e, ~ (X (0%nat)).(info_ctrl_srcs) e) /\
  agree_regs (X (0%nat)).(info_regs) regs /\
  forall (n : nat),
  let Xnow := X n in
  match Xnow.(info_tr) with
  | [] =>
    match next_pc regs with
    | None => False (* what does this correspond to? *)
    | Some (addr, _) =>
      let e := (tid, Xnow.(info_cur_eid)) in
      exists v tr',
        pe.(pe_lab) e = Fetch addr v /\
        List.In tr' (decode v) /\
        let Xnext := Xnow <| info_tr := tr' |>
          <| info_cur_eid := (Xnow.(info_cur_eid) + 1)%nat |>
          <| info_fe_src := Xnow.(info_cur_eid) |>
          <| info_ctrl_srcs := Xnow.(info_ctrl_srcs) |> in
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
        let e := (tid, Xnow.(info_cur_eid)) in
        let Xnext := Xnow <| info_ctrl_srcs := (fun e' => snd e = e' \/ Xnow.(info_ctrl_srcs) e') |> in
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
        pe.(pe_lab) e = Act a /\
        let Xnext := Xnow <| info_tr := tr' |>
          <| info_cur_eid := (Xnow.(info_cur_eid) + 1)%nat |> in
        pe.(pe_fe) (tid, Xnow.(info_fe_src)) e /\
        (forall e', pe.(pe_fe) e' e -> e' = (tid, Xnow.(info_fe_src))) /\
        (forall e', Xnow.(info_ctrl_srcs) e' -> pe.(pe_ctrl) (tid, e') e) /\
        (forall e', pe.(pe_ctrl) e' e -> exists e'', Xnow.(info_ctrl_srcs) e'' /\ e' = (tid, e'')) /\
        (forall e', Xnow.(info_data_srcs) e' -> (tid, e') <> e -> pe.(pe_data) (tid, e') e) /\
        (forall e', pe.(pe_data) e' e -> exists e'', Xnow.(info_data_srcs) e'' /\ e' = (tid, e'') /\ e' <> e) /\
        info_agrees Xnext (X (n+1)%nat)
      | Some (LDone _) => False (* right? *)
      | Some (LAssert b) => b = true
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
  (* TODO: or should it build execution witnesses explicitly? *)
}.

Require Import Coq.Relations.Relation_Operators.

Definition acyclic (r : event_id -> event_id -> Prop) : Prop :=
  Irreflexive (clos_trans _ r).

Definition wf_rf (pe : pre_execution) (rf : event_id -> event_id -> Prop) :=
  (forall e,
    match pe.(pe_lab) e with
    | Act (LReadMem v _ addr _ _) =>
      (exists w, rf w e /\
        match pe.(pe_lab) e with
        | Act (LWriteMem _ _ addr' v' _ _) => addr = addr' /\ v = v'
        | _ => False
        end) /\
      (forall w1 w2, rf w1 e -> rf w2 e -> w1 = w2)
    | _ => ~ (exists e', rf e' e)
    end).

Definition wf_irf (pe : pre_execution) (irf : event_id -> event_id -> Prop) : Prop :=
  True (* TODO *).


Definition wf_co (pe : pre_execution) (co : event_id -> event_id -> Prop) : Prop :=
  (forall e e',
    match pe.(pe_lab) e, pe.(pe_lab) e' with
    | Act (LWriteMem _ _ addr1 _ _ _), Act (LWriteMem _ _ addr2 _ _ _) =>
      addr1 = addr2 -> co e e' \/ co e' e
    | _, _ => False
    end) /\
  Transitive co /\
  Irreflexive co /\
  (forall e tid e', co e (tid, e') -> tid <> 0%nat).

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

(* TODO: allow for initial state? *)
Definition valid_execution_of (regss : list reg_map) (pe0 : pre_execution) (pe : pre_execution) (mm : memory_model) : Prop :=
  (* TODO: pe0 included in pe *)
  pre_execution_of_threads regss pe /\
  mm.(mm_validity) pe.