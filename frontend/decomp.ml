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
  Filename.concat Config.etc "aarch65_isla_coq.toml"

let rec split_instr s =
  if String.equal s "" then
    []
  else
    let rest = String.sub s 2 ((String.length s) - 2) in
    String.sub s 0 2 :: (split_instr rest)

let instr_rev i =
  let split = split_instr i in
  String.concat "" (List.rev split)

let get_constraint_str derefs =
  if derefs = "" then
    ""
  else
    let derefs = List.map String.trim (String.split_on_char ';' derefs) in
    let constraints = List.map (fun d -> "--reset-constraint '= (bvand " ^ d ^ " 0xfff0000000000007) 0x0000000000000000'") derefs in
    String.concat " " constraints

let process_line line addrs =
  let cols = String.split_on_char ':' line in
  let addr = String.trim (List.nth cols 0) in
  let instr = instr_rev (String.trim (List.nth cols 1)) in
  let derefs = String.trim (List.nth cols 2) in
  let addr_name = "a" ^ addr in
  let isla_file = addr_name ^ ".isla" in
  let coq_file = addr_name ^ ".v" in
  let constraint_str = get_constraint_str derefs in
  let command =
    Printf.sprintf "./run_isla_footprint.sh -f isla_footprint_no_init \
      -C %s --simplify-registers -s -x -i %s %s > %s" aarch64_isla_coq instr
      constraint_str isla_file
  in
  ignore (Sys.command command);
  gen_coq addr_name isla_file coq_file;
  addr :: addrs

let output_instr_map addrs oc =
  let p fmt = Printf.fprintf oc fmt in
  p "From isla Require Import isla_lang.\n"; (* I don't know why we need this, but without it I get a weird parser error from coq *)
  List.iter (fun a -> p "Require Import a%s.\n" a) addrs;
  p "\n\nDefinition instr_map := [";
  match addrs with
  | [] -> p "]." (* Probably means something went wrong, maybe should raise? *)
  | a :: addrs ->
    p "\n(0x%s%%Z, a%s)\n" a a;
    List.iter (fun a -> p "; (0x%s%%Z, a%s)\n" a a) addrs;
    p "]."

let process_file filename =
  let lines = read_file filename in
  let addrs = List.fold_right process_line lines [] in
  let instr_map_oc = open_out "instrs.v" in
  output_instr_map addrs instr_map_oc;
  close_out instr_map_oc