open Isla_lang
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

(** Representation of a line of (annotated) objdump output. *)
type decomp_line = {
  dl_addr      : string;
  dl_opcode    : string; (* The opcode from objdump. *)
  dl_revopcode : string; (* Reversed version (other endianness). *)
  dl_constrs   : string list;
  dl_instr     : string;
  dl_comment   : string option;
}

let name_from_template : Template.t -> decomp_line -> string = fun t d ->
  let map = SMap.empty in
  let map = SMap.add "addr"  d.dl_addr      map in
  let map = SMap.add "op"    d.dl_opcode    map in
  let map = SMap.add "revop" d.dl_revopcode map in
  try Template.subst t map with Invalid_argument(_) ->
    assert false (* Unreachable. *)

(** [parse_decomp input_file] parses lines of [input_file] to obtain a list of
    instruction lines to be processed. Empty lines are ignored, and in case of
    an error the whole program is interupted. *)
let parse_decomp : string -> decomp_line list = fun input_file ->
  (* Get all non-empty lines of the input file, with the line number. *)
  let lines =
    let lines =
      try read_file input_file with Sys_error(_) ->
        panic "Cannot open file \"%s\"." input_file
    in
    let lines = List.mapi (fun i line -> (i+1, String.trim line)) lines in
    List.filter (fun (_, line) -> line <> "") lines
  in
  (* Do the parsing. *)
  let parse_line (i, line) =
    let parse_error fmt =
      let fmt = "Parse error in file \"%s\", line %i: " ^^ fmt ^^ "." in
      panic fmt input_file i
    in
    let cols = String.split_on_char ':' line in
    let cols = List.map String.trim cols in
    let (addr, opcode, constrs, instr) =
      match cols with
      | [addr; op; constrs; instr] -> (addr, op, constrs, instr)
      | _                          ->
      let nb_cols = List.length cols in
      parse_error "wrong number of columns (%i instead of 4)." nb_cols
    in
    let is_hex c = match c with '0'..'9' | 'a'..'f' -> true | _ -> false in
    (* Sanity check for the address. *)
    let dl_addr =
      if addr = "" then
        parse_error "the first column is empty (expected hex address)";
      if not (String.for_all is_hex addr) then
        parse_error "the second column is should be an hex address";
      addr
    in
    (* Sanity check and endianness fix for the opcode. *)
    let dl_opcode = opcode in
    let dl_revopcode =
      if opcode = "" then
        parse_error "the second column is empty (expected hex op-code)";
      if not (String.for_all is_hex opcode) then
        parse_error "the second column should be an hex op-code";
      let reverse_bytes s =
        let bs =
          try String.chop 2 s with Invalid_argument(_) ->
            panic "the op-code in second column has an odd number of digits"
        in
        String.concat "" (List.rev bs)
      in
      reverse_bytes opcode
    in
    (* Build the list of constraints. *)
    let dl_constrs =
      let constrs = String.split_on_char ';' constrs in
      match constrs with [""] -> [] | _ -> List.map String.trim constrs
    in
    (* Split the instruction and possible comments. *)
    let (dl_instr, dl_comment) =
      let pieces = String.split_on_char '/' instr in
      let rec find_comment acc pieces =
        match pieces with
        | []              -> (String.concat "/" (List.rev acc), None)
        | piece :: pieces ->
        if piece <> "" then
          find_comment (piece :: acc) pieces
        else
          (* Reached a comment. *)
          let instr = String.concat "/" (List.rev acc) in
          let comment = String.concat "/" pieces in
          (String.trim instr, Some(String.trim comment))
      in
      find_comment [] pieces
    in
    (* Remove random tabs from the instruction. *)
    let dl_instr = String.concat " " (String.split_on_char '\t' dl_instr) in
    {dl_addr; dl_opcode; dl_revopcode; dl_constrs; dl_instr; dl_comment}
  in
  List.map parse_line lines

let process_line : Template.t -> string -> decomp_line -> unit =
    fun name_template output_dir d ->
  let name = name_from_template name_template d in
  let isla_file = Filename.concat output_dir (name ^ ".isla") in
  let coq_file  = Filename.concat output_dir (name ^ ".v"   ) in
  let constrs =
    let constr_to_string = Printf.sprintf "--reset-constraint '%s'" in
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

let gen_instr_map : Template.t -> string list -> decomp_line list
    -> Format.formatter -> unit = fun name_template coq_prefix lines ff ->
  let pp fmt = Format.fprintf ff fmt in
  (* Imports. *)
  pp "From isla Require Import isla_lang.@."; (* Required for notations. *)
  let pp_export d =
    let name = name_from_template name_template d in
    pp "Require Export %s.@." (String.concat "." (coq_prefix @ [name]))
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
  let lines = parse_decomp input_file in
  List.iter (process_line name_template output_dir) lines;
  (* Generate ["instrs.v"] file. *)
  let instrs_file = Filename.concat output_dir "instrs.v" in
  let writer = gen_instr_map name_template coq_prefix lines in
  Format.write_file instrs_file writer;
  (* Generate the ["dune"] file. *)
  let dune_file = Filename.concat output_dir "dune" in
  Format.write_file dune_file (gen_dune coq_prefix)
