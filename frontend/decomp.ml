let input_line_opt ic =
  try
    Some (input_line ic)
  with e ->
    None

let rec read_lines ic =
  match input_line_opt ic with
  | Some line ->
    line :: (read_lines ic)
  | None ->
    []

let ignored_registers =
  [
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
    "__highest_el_aarch32"
  ]

let ignored_words =
  ["Cycle"] @ 
  List.map (fun reg -> "ReadReg \"" ^ reg ^ "\"") ignored_registers @
  List.map (fun reg -> "WriteReg \"" ^ reg ^ "\"") ignored_registers

let contains_string haystack needle =
  try ignore(Str.search_forward (Str.regexp_string needle) haystack 0 : int); true
  with e -> false

let contains_ignored_word line =
  match List.find_opt (fun word -> contains_string line word) ignored_words with
  | Some _ -> true
  | None -> false

let filter_ignored_words lines =
  let f l = not (contains_ignored_word l) in
  List.filter f lines

let filter_file filename =
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  let lines = filter_ignored_words lines in
  let oc = open_out filename in
  List.iter (Printf.fprintf oc "%s\n") lines;
  close_out oc

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
    ("./run_isla_footprint.sh -f isla_footprint_no_init --simplify-registers -s -x -i " ^ instr ^ " " ^ constraint_str ^ " > " ^ isla_file)
  in
  let _ : int = Sys.command command in
  let conf : Of_isla.config = { input_file = isla_file; output_file = Some coq_file; definition_name = addr_name} in
  Of_isla.run conf;
  filter_file coq_file;
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
  let ic = open_in filename in
  let lines = read_lines ic in
  close_in ic;
  let addrs = List.fold_right process_line lines [] in
  let instr_map_oc = open_out "instrs.v" in
  output_instr_map addrs instr_map_oc;
  close_out instr_map_oc


