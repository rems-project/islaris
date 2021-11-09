open Isla_lang_if
open Parse_dump
open Extra
open Arch

(** [event_filter arch e] returns true for all events that are not "Cycle" and
    that are not operations on ingnored registers for architecture [arch]. *)
let event_filter : Arch.t -> event -> bool = fun arch e ->
  let open Ast in
  match e with
  | AssumeReg(n,_,_,_)
  | ReadReg(n,_,_,_)
  | WriteReg(n,_,_,_)     -> not (List.mem n arch.arch_ignored_regs)
  | Cycle(_)              -> false
  | MarkReg(_, _, _)      -> false
  | Smt(DefineEnum(_), _) -> false
  | _                     -> true

(** [gen_coq arch name isla_f coq_f] processes Isla file [isla_f] and produces
    a corresponding Coq file [coq_f] whose main definition is named [name]. In
    the process, architecture [arch] is used to determine which events most be
    filtered. In case of error, the program is terminated using [panic]. *)
let gen_coq : Arch.t -> string -> string -> string -> unit =
    fun arch name isla_f coq_f ->
  (* Parsing the isla file. *)
  let trs =
    try Parser.parse_file isla_f with Parser.Parse_error(msg) ->
      panic "Error while parsing [%s].\n%s" isla_f msg
  in
  (* Filtering the events to minimise the trace. *)
  let trs = filter_events (event_filter arch) trs in
  (* Generating the Coq file. *)
  Coq_pp.write_trace name trs (Some(coq_f))

(** Keys allowed in name templates. *)
let template_keys : (string * string) list = [
  ("addr" , "address of the instruction");
  ("op"   , "opcode of the instruction" );
  ("revop", "reversed opcode of the instruction");
  ("instr", "instruction mnemonic");
]

let default_template : string = "a{addr}"

let name_from_template : Template.t -> decomp_line -> string = fun t d ->
  let instr_mnem = List.hd (String.split_on_char ' ' d.dl_instr) in
  let map = SMap.empty in
  let map = SMap.add "addr"  d.dl_addr      map in
  let map = SMap.add "op"    d.dl_opcode    map in
  let map = SMap.add "revop" d.dl_revopcode map in
  let map = SMap.add "instr" instr_mnem     map in
  try Template.subst t map with Invalid_argument(_) ->
    assert false (* Unreachable. *)

type task = {
  task_command   : string;
  (** Command to run. *)
  task_name      : string;
  (** Specialization of the name template for the task. *)
  task_isla_file : string;
  (** Isla file being generated by the command. *)
  task_coq_file  : string;
  (** Coq file to generate from the Isla file. *)
  task_arch      : Arch.t;
  (** Architecture assumed for the task. *)
}

let build_task : Arch.t -> Template.t -> string -> decomp_line -> task =
    fun task_arch name_template output_dir d ->
  let task_name = name_from_template name_template d in
  let task_isla_file = Filename.concat output_dir (task_name ^ ".isla") in
  let task_coq_file  = Filename.concat output_dir (task_name ^ ".v"   ) in
  let constrs =
    let constr_to_string (_, _, constr) =
      Printf.sprintf "--reset-constraint '%s'" constr
    in
    String.concat " " (List.map constr_to_string d.dl_constrs)
  in
  let linearize =
    let args = List.map (Printf.sprintf "--linearize %s") d.dl_linearize in
    String.concat " " args
  in
  let task_command =
    Printf.sprintf "isla-footprint %s -f isla_footprint_no_init \
      -C %s --simplify-registers --tree -s -x -i %s %s %s > %s 2> /dev/null"
      task_arch.arch_snapshot_file task_arch.arch_isla_config
      d.dl_revopcode constrs linearize task_isla_file
  in
  {task_command; task_name; task_isla_file; task_coq_file; task_arch}

let run_tasks : int -> task list -> unit = fun j tasks ->
  let errored = ref false in
  let run_task i with_io_lock task =
    let command   = task.task_command in
    let name      = task.task_name in
    let isla_file = task.task_isla_file in
    let coq_file  = task.task_coq_file in
    let info fmt = Format.printf ("(thread %i) " ^^ fmt ^^ "\n%!") i in
    with_io_lock (fun () -> info "[isla-footprint] %s" isla_file);
    match Sys.command task.task_command with
    | 0 ->
        with_io_lock (fun () -> info "[coq-generation] %s" coq_file);
        gen_coq task.task_arch name isla_file coq_file
    | i ->
        errored := true;
        with_io_lock (fun () ->
          info (Color.red "Error while generating file \"%s\".") coq_file;
          info "Command [%s] terminated with code %i." command i)
  in
  Parallel.iter j run_task tasks;
  if !errored then
    panic "There were errors while running isla-footprint."

let gen_instr_file : Template.t -> string list -> decomp_line list
    -> Format.formatter -> unit = fun name_template coq_prefix lines ff ->
  let pp fmt = Format.fprintf ff fmt in
  (* Imports. *)
  pp "Require Import isla.isla_lang.@."; (* Required for notations. *)
  let pp_export d =
    let name = name_from_template name_template d in
    let build_mp name = String.concat "." (coq_prefix @ [name]) in
    pp "Require Export %s.@." (build_mp name);
    if d.dl_spec <> None then
      pp "Require Export %s.@." (build_mp (name ^ "_spec"))
  in
  List.iter pp_export lines;
  (* Definition. *)
  pp "@.Definition instr_map := [";
  let pp_sep ff _ = Format.fprintf ff ";" in
  let pp_elt ff d =
    Format.fprintf ff "@.  (0x%s%%Z, %s (* %s *))" d.dl_addr
      (name_from_template name_template d) d.dl_instr
  in
  pp "%a" (Format.pp_print_list ~pp_sep pp_elt) lines;
  if lines <> [] then pp "@.";
  pp "].@."

let gen_spec_file : Arch.t -> Template.t -> string -> string list
    -> decomp_line  -> unit =
    fun arch name_template output_dir coq_prefix d ->
  (* Only generate a file if there is a spec. *)
  match d.dl_spec with None -> () | Some(spec) ->
  let name = name_from_template name_template d in
  let write_spec ff =
    let pp fmt = Format.fprintf ff fmt in
    (* Imports. *)
    pp "Require Import isla.isla.@.";
    pp "Require Import isla.%s.%s.@." arch.arch_coq_name arch.arch_coq_name;
    let build_mp name = String.concat "." (coq_prefix @ [name]) in
    pp "Require Export %s.@." (build_mp name);
    List.iter (pp "Require Import %s.@.") spec.spec_imports;
    (* Lemma. *)
    pp "@.Lemma %s_spec `{!islaG Σ} `{!threadG} pc:@." name;
    pp "  instr pc (Some %s) -∗@." name;
    pp "  instr_body pc (%s).@." spec.spec_spec;
    pp "Proof.@.";
    if spec.spec_admitted then
      pp "Admitted.@."
    else begin
      pp "  iStartProof.@.";
      pp "  repeat liAStep; liShow.@.";
      pp "  Unshelve. all: prepare_sidecond.@.";
      List.iter (pp "  %s@.") spec.spec_tactics;
      pp "Qed.@."
    end;
    (* SimplifyHyp rule. *)
    pp "@.Definition %s_spec_inst `{!islaG Σ} `{!threadG} pc :=@." name;
    pp "  entails_to_simplify_hyp 0 (%s_spec pc).@." name;
    pp "Global Existing Instance %s_spec_inst.@." name
  in
  let spec_file = Filename.concat output_dir (name ^ "_spec.v") in
  Format.write_file spec_file write_spec

let gen_dune : Arch.t -> string list -> Format.formatter -> unit =
    fun arch coq_prefix ff ->
  let pp fmt = Format.fprintf ff fmt in
  pp "; Generated by [isla-coq], do not edit.@.";
  pp "(coq.theory@.";
  pp " (name %s)@." (String.concat "." coq_prefix);
  pp " (package coq-isla)@.";
  pp " (flags -w -notation-overridden -w -redundant-canonical-projection)@.";
  pp " (synopsis \"Generated file\")@.";
  pp " (theories isla isla.%s))@." arch.arch_coq_name

(* Entry point. *)
let run arch name_template output_dir coq_prefix nb_jobs input_file =
  (* Process the decompilation file. *)
  let lines = Parse_dump.parse input_file in
  (* Run isla-footprint on the instructions. *)
  let build_task = build_task arch name_template output_dir in
  run_tasks nb_jobs (List.map build_task lines);
  (* Generate the ["<NAME>_spec.v"] files. *)
  List.iter (gen_spec_file arch name_template output_dir coq_prefix) lines;
  (* Generate ["instrs.v"] file. *)
  let instrs_file = Filename.concat output_dir "instrs.v" in
  let writer = gen_instr_file name_template coq_prefix lines in
  Format.write_file instrs_file writer;
  (* Generate the ["dune"] file. *)
  let dune_file = Filename.concat output_dir "dune" in
  Format.write_file dune_file (gen_dune arch coq_prefix)
