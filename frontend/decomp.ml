open Isla_lang
open Extra

(** [ignored_registers] is a list of registers for which read and write events
    are removed from the trace. *)
let ignored_registers = [
  "SEE";
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

(** Representation of a line of (annotated) objdump output. *)
type decomp_line = {
  dl_addr    : string;
  dl_opcode  : string;
  dl_constrs : string list;
  dl_instr   : string;
  dl_comment : string option;
}

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
    let dl_opcode =
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
    {dl_addr; dl_opcode; dl_constrs; dl_instr; dl_comment}
  in
  List.map parse_line lines

let process_line : (string -> string -> string) -> string -> decomp_line
    -> unit = fun name_template output_dir d ->
  let name = name_template d.dl_addr d.dl_instr in
  let isla_file = Filename.concat output_dir (name ^ ".isla") in
  let coq_file  = Filename.concat output_dir (name ^ ".v"   ) in
  let constrs =
    let constr_to_string c =
      "--reset-constraint '= (bvand " ^ c ^
      " 0xfff0000000000007) 0x0000000000000000'"
    in
    String.concat " " (List.map constr_to_string d.dl_constrs)
  in
  let command =
    Printf.sprintf "isla-footprint -f isla_footprint_no_init \
      -C %s --simplify-registers -s -x -i %s %s > %s" aarch64_isla_coq
      d.dl_opcode constrs isla_file
  in
  match Sys.command command with
  | 0 -> gen_coq name isla_file coq_file
  | i -> panic "Command [%s] terminated with code %i." command i

(* TODO somehow use a correct Coq module path for the imports. *)
let output_instr_map : (string -> string -> string) -> decomp_line list
    -> Format.formatter -> unit = fun name_template lines ff ->
  let pp fmt = Format.fprintf ff fmt in
  (* Imports. *)
  pp "From isla Require Import isla_lang.@."; (* Required for notations. *)
  let pp_import d =
    pp "Require Import %s.@." (name_template d.dl_addr d.dl_instr)
  in
  List.iter pp_import lines;
  (* Definition. *)
  pp "@.Definition instr_map := [";
  let pp_sep ff _ = Format.fprintf ff ";" in
  let pp_elt ff d =
    Format.fprintf ff "@.  (0x%s%%Z, %s (* %s *))" d.dl_addr
      (name_template d.dl_addr d.dl_instr) d.dl_instr
  in
  pp "%a" (Format.pp_print_list ~pp_sep pp_elt) lines;
  if lines <> [] then pp "@.";
  pp "].@."

(* TODO also generate a dune file? *)
let run name_template output_dir input_file =
  let lines = parse_decomp input_file in
  List.iter (process_line name_template output_dir) lines;
  let instrs_file = Filename.concat output_dir "instrs.v" in
  Format.write_file instrs_file (output_instr_map name_template lines)
