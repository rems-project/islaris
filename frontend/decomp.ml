open Isla_lang_if
open Parse_dump
open Extra

(** [ignored_registers] is a list of registers for which read and write events
    are removed from the trace. *)
let ignored_registers = [
  "SEE";
  "BTypeNext";
  "__unconditional";
  "__v81_implemented";
  "__v82_implemented";
  "__v83_implemented";
  "__v84_implemented";
  "__v85_implemented";
  "__trickbox_enabled";
  "__CNTControlBase";
  "__defaultRAM";
  "__isla_monomorphize_reads";
  "__isla_monomorphize_writes";
  "__highest_el_aarch32";
]

(** [event_filter e] returns true for all events that are not "Cycle" and that
    are not register operations for registers in [ignored_registers]. *)
let event_filter : event -> bool = fun e ->
  let open Ast in
  match e with
  | ReadReg(n,_,_,_)
  | WriteReg(n,_,_,_) -> not (List.mem n ignored_registers)
  | Cycle(_)          -> false
  | MarkReg(_, _, _)  -> false
  | _                 -> true

(** [gen_coq name isla_f coq_f] processes the Isla file [isla_f] and generates
    a corresponding Coq file [coq_f] whose main definition is named [name]. In
    case of an error, the whole program is terminated using [panic]. *)
let gen_coq : string -> string -> string -> unit = fun name isla_f coq_f ->
  (* Parsing the isla file. *)
  let trs =
    try Parser.parse_file isla_f with Parser.Parse_error(msg) ->
      panic "Error while parsing [%s].\n%s" isla_f msg
  in
  (* Filtering the events to minimise the trace. *)
  let trs = filter_events event_filter trs in
  (* Generating the Coq file. *)
  Coq_pp.write_traces name trs (Some(coq_f))

(** Absolute path to the aarch64 isla configuration file. *)
let aarch64_isla_coq : Filename.filepath =
  Filename.concat Config.etc "aarch64_isla_coq.toml"

(** Keys allowed in name templates. *)
let template_keys : (string * string) list = [
  ("addr" , "address of the instruction");
  ("op"   , "opcode of the instruction" );
  ("revop", "reversed opcode of the instruction");
]

let default_template : string = "a{addr}"

let name_from_template : Template.t -> decomp_line -> string = fun t d ->
  let map = SMap.empty in
  let map = SMap.add "addr"  d.dl_addr      map in
  let map = SMap.add "op"    d.dl_opcode    map in
  let map = SMap.add "revop" d.dl_revopcode map in
  try Template.subst t map with Invalid_argument(_) ->
    assert false (* Unreachable. *)

let process_line : Template.t -> string -> decomp_line -> unit =
    fun name_template output_dir d ->
  let name = name_from_template name_template d in
  let isla_file = Filename.concat output_dir (name ^ ".isla") in
  let coq_file  = Filename.concat output_dir (name ^ ".v"   ) in
  let constrs =
    let constr_to_string (_, _, constr) =
      Printf.sprintf "--reset-constraint '%s'" constr
    in
    String.concat " " (List.map constr_to_string d.dl_constrs)
  in
  let command =
    Printf.sprintf "isla-footprint -f isla_footprint_no_init \
      -C %s --simplify-registers -s -x -i %s %s > %s" aarch64_isla_coq
      d.dl_revopcode constrs isla_file
  in
  match Sys.command command with
  | 0 -> gen_coq name isla_file coq_file
  | i -> panic "Command [%s] terminated with code %i." command i

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

let gen_spec_file : Template.t -> string -> string list -> decomp_line
    -> unit = fun name_template output_dir coq_prefix d ->
  (* Only generate a file if there is a spec. *)
  match d.dl_spec with None -> () | Some(spec) ->
  let name = name_from_template name_template d in
  let write_spec ff =
    let pp fmt = Format.fprintf ff fmt in
    (* Imports. *)
    pp "Require Import isla.isla.@.";
    List.iter (pp "Require Import %s.@.") spec.spec_imports;
    (* Lemma. *)
    pp "@.Lemma %s_spec `{!islaG Σ} `{!threadG}:@." name;
    pp "  instr 0x%s (Some %s) -∗@." d.dl_real_addr name;
    pp "  instr_body 0x%s (%s).@." d.dl_real_addr spec.spec_spec;
    pp "Proof.@.";
    pp "  iStartProof.@.";
    pp "  repeat liAStep; liShow.@.";
    pp "  Unshelve. all: prepare_sidecond.@.";
    List.iter (pp "  %s@.") spec.spec_tactics;
    pp "%s.@." (if spec.spec_admitted then "Admitted" else "Qed")
  in
  let spec_file = Filename.concat output_dir (name ^ "_spec.v") in
  Format.write_file spec_file write_spec

let gen_dune : string list -> Format.formatter -> unit = fun coq_prefix ff ->
  let pp fmt = Format.fprintf ff fmt in
  pp "; Generated by [isla-coq], do not edit.@.";
  pp "(coq.theory@.";
  pp " (name %s)@." (String.concat "." coq_prefix);
  pp " (package coq-isla)@.";
  pp " (flags -w -notation-overridden -w -redundant-canonical-projection)@.";
  pp " (synopsis \"Generated file\")@.";
  pp " (theories isla))@."

(* Entry point. *)
let run name_template output_dir coq_prefix input_file =
  (* Process the decompilation file and run isla-footprint. *)
  let lines = Parse_dump.parse input_file in
  List.iter (process_line name_template output_dir) lines;
  (* Generate the ["<NAME>_spec.v"] files. *)
  List.iter (gen_spec_file name_template output_dir coq_prefix) lines;
  (* Generate ["instrs.v"] file. *)
  let instrs_file = Filename.concat output_dir "instrs.v" in
  let writer = gen_instr_file name_template coq_prefix lines in
  Format.write_file instrs_file writer;
  (* Generate the ["dune"] file. *)
  let dune_file = Filename.concat output_dir "dune" in
  Format.write_file dune_file (gen_dune coq_prefix)
