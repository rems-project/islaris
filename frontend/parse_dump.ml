open Extra
open Unsigned

(** [uint64_to_hex_string i] converts integer [i] into its hexadecimal, string
    representation. *)
let uint64_to_hex_string : uint64 -> string = fun i ->
  let open UInt64 in
  let chunk_mask = of_int 0xFFFF in
  let i1 = to_int (logand (shift_right i 48) chunk_mask) in
  let i2 = to_int (logand (shift_right i 32) chunk_mask) in
  let i3 = to_int (logand (shift_right i 16) chunk_mask) in
  let i4 = to_int (logand (shift_right i  0) chunk_mask) in
  let is = Printf.sprintf "%x%x%x%x" i1 i2 i3 i4 in
  let len = String.length is in
  let first_non_0 =
    let i = ref 0 in
    while !i < len && is.[!i] = '0' do incr i done; !i
  in
  if first_non_0 = len then "0" else
    String.sub is first_non_0 (len - first_non_0)

(** Hexadecimal address as a string. *)
type address = string

(** Label as a string. *)
type label = string

(** Representation of a standard objdump line containing an instruction. *)
type instr_line = {
  instr_addr      : uint64;
  instr_opcode    : string;
  instr_revopcode : string;
  instr_instr     : string;
  instr_comment   : string option;
}

(** Representation of an isla-coq annotation. *)
type annot = {
  annot_tag     : string;
  annot_payload : string option;
}

(** Possible kind of lines in an annotatied decompilation file. *)
type line_kind =
  | Line_blank of string option
  (** Blank line, comment contents if any. *)
  | Line_annot of annot
  (** Annotation comment with tag and payload if any. *)
  | Line_label of address * label
  (** Standard objdump line containing a label (at given address). *)
  | Line_instr of instr_line
  (** Standard objdump line containing an instruction. *)

(** Line-based position information attached to data. *)
type 'a line_pos = {
  line_file : Filename.filepath;
  line_num  : int;
  line_orig : string;
  line_data : 'a;
}

(** A single line from an annotated decompilation file. *)
type line = line_kind line_pos

(** [pre_parse input_file] roughly parses file [input_file] processing each of
    its lines independently. *)
let pre_parse : Filename.filepath -> line list = fun input_file ->
  let is_hex c = match c with '0'..'9' | 'a'..'f' -> true | _ -> false in
  let pre_parse_line line_num_minus_one line_orig =
    let line_num = line_num_minus_one + 1 in
    let no_parse fmt =
      let fmt = "Parse error in file \"%s\", at line %i.\n" ^^ fmt in
      panic fmt input_file line_num
    in
    let line_data =
      let s = String.trim line_orig in
      let len = String.length s in
      if len = 0 then
        (* Empty line. *)
        Line_blank(None)
      else if len > 3 && String.sub s 0 3 = "//@" then
        (* Annotation. *)
        match String.index_opt s ':' with
        | None    ->
            (* No payload. *)
            let annot_tag = String.sub s 3 (len - 3) in
            (* TODO some validation. *)
            Line_annot({annot_tag; annot_payload = None})
        | Some(i) ->
            (* There is a payload. *)
            let annot_tag = String.trim (String.sub s 3 (i - 3)) in
            (* TODO some validation. *)
            let p = String.trim (String.sub s (i + 1) (len - i - 1)) in
            Line_annot({annot_tag; annot_payload = Some(p)})
      else if len > 2 && String.sub s 0 2 = "//" then
        (* Comment. *)
        let text = String.trim (String.sub s 2 (len - 2)) in
        Line_blank(Some(text))
      else if len > 2 && String.sub s (len - 2) 2 = ">:" then
        (* Label. *)
        let i =
          try String.index s '<' with Not_found ->
            no_parse "Cannot find token '<' in the label line."
        in
        let addr = String.trim (String.sub s 0 (i - 1)) in
        let label = String.trim (String.sub s (i + 1) (len - i - 3)) in
        (* TODO some validation. *)
        Line_label(addr, label)
      else
        (* Instruction *)
        let (instr_addr, s) =
          let i =
            try String.index s ':' with Not_found ->
              no_parse "Cannot find token ':' in the instruction line."
          in
          let addr = String.trim (String.sub s 0 i) in
          (addr, String.trim (String.sub s (i + 1) (len - i - 1)))
        in
        let len = String.length s in
        let (instr_opcode, s) =
          let i =
            try String.index s ' '  with Not_found ->
            try String.index s '\t' with Not_found ->
              no_parse "Cannot separate the opcode from the instruction."
          in
          let op = String.trim (String.sub s 0 i) in
          (op, String.trim (String.sub s (i + 1) (len - i - 1)))
        in
        let len = String.length s in
        let (instr_instr, instr_comment) =
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
          find_comment [] (String.split_on_char '/' s)
        in
        (* Remove random tabs from the instruction. *)
        let instr_instr =
          String.concat " " (String.split_on_char '\t' instr_instr)
        in
        (* Check the address. *)
        let instr_addr =
          if instr_addr = "" then
            no_parse "The address (before the ':') is empty.";
          if not (String.for_all is_hex instr_addr) then
            no_parse "The address (before the ':') should be a hex number.";
          try UInt64.of_string ("0x" ^ instr_addr) with Failure(_) ->
            no_parse "The address (before the ':') does not fit on 64 bits."
        in
        (* Check the opcode and create a version of the other endianness. *)
        let instr_revopcode =
          if instr_opcode = "" then
            no_parse "The opcode (after the ':') is empty.";
          if not (String.for_all is_hex instr_opcode) then
            no_parse "The opcode (after the ':') should be a hex number.";
          let reverse_bytes s =
            let bs =
              try String.chop 2 s with Invalid_argument(_) ->
              panic "The opcode (after the ':') has an odd number of digits"
            in
            String.concat "" (List.rev bs)
          in
          reverse_bytes instr_opcode
        in
        let instr =
          {
            instr_addr;
            instr_opcode;
            instr_revopcode;
            instr_instr;
            instr_comment;
          }
        in
        Line_instr(instr)
    in
    {line_file = input_file; line_num; line_orig; line_data}
  in
  let lines =
    try read_file input_file with Sys_error(_) ->
      panic "Cannot open file \"%s\"." input_file
  in
  List.mapi pre_parse_line lines

(** Representation of an annotated, decompiled instruction. *)
type decomp_line = {
  dl_from_file : Filename.filepath;
  dl_from_line : int;
  dl_line_orig : string;
  dl_addr      : string;
  dl_opcode    : string; (* The opcode from objdump. *)
  dl_revopcode : string; (* Reversed version (other endianness). *)
  dl_constrs   : (int * string * string) list; (* Holds: (line, orig, c). *)
  dl_instr     : string;
  dl_comment   : string option;
}

(** [parse input_file] parses file [input_file] to obtain a list of annotated,
    decompiled instructions. *)
let parse : Filename.filepath -> decomp_line list = fun input_file ->
  let no_parse (pos : _ line_pos) fmt =
    let fmt = "Parse error in file \"%s\", at line %i.\n" ^^ fmt in
    panic fmt pos.line_file pos.line_num
  in
  let flush_annots annots =
    match annots with [] -> () | annot :: _ ->
    no_parse annot "This annotation is not attached to an instruction."
  in
  let build_decomp_line annots line =
    let constrs =
      let build_constr annot =
        let constr =
          let tag = annot.line_data.annot_tag in
          let payload = annot.line_data.annot_payload in
          match (tag, payload) with
          | ("constraint", Some(constr)) -> constr
          | ("constraint", None        ) ->
              no_parse annot "Annotation \"%s\" must have a payload." tag
          | (_           , _           ) ->
              no_parse annot "Unknown annotation tag \"%s\"." tag
        in
        (annot.line_num, annot.line_orig, constr)
      in
      List.map build_constr annots
    in
    {
      dl_from_file = line.line_file;
      dl_from_line = line.line_num;
      dl_line_orig = line.line_orig;
      dl_addr      = uint64_to_hex_string line.line_data.instr_addr;
      dl_opcode    = line.line_data.instr_opcode;
      dl_revopcode = line.line_data.instr_revopcode;
      dl_constrs   = constrs;
      dl_instr     = line.line_data.instr_instr;
      dl_comment   = line.line_data.instr_comment;
    }
  in
  let rec build annots acc lines =
    match lines with
    | []            -> flush_annots (List.rev annots); List.rev acc
    | line :: lines ->
    match line.line_data with
    (* Empty line or label flushes the annotations, if any. *)
    | Line_blank(None)
    | Line_label(_)       ->
        flush_annots (List.rev annots);
        build [] acc lines
    (* Comments are ignored. *)
    | Line_blank(Some(_)) ->
        build annots acc lines
    (* Accumulate annotations. *)
    | Line_annot(a)       ->
        build ({line with line_data = a} :: annots) acc lines
    (* Build a line, collecting annotations. *)
    | Line_instr(i)       ->
        let dl =
          let i = {line with line_data = i} in
          build_decomp_line (List.rev annots) i
        in
        build [] (dl :: acc) lines
  in
  build [] [] (pre_parse input_file)

(** [parse_and_pp_debug oc input_file] parses file [input_file] and then print
    various debugging information for the parser. *)
let parse_and_pp_debug : out_channel -> Filename.filepath -> unit =
    fun oc input_file ->
  let info fmt = Printf.fprintf oc (fmt ^^ "\n%!") in
  info "Reading file \"%s\"." input_file;
  let lines = pre_parse input_file in
  info "==== parsed lines ====";
  let print_line l =
    match l.line_data with
    | Line_blank(None)    -> info "blank"
    | Line_blank(Some(s)) -> info "comment(%s)" s
    | Line_label(a,l)     -> info "label(%s, %s)" a l
    | Line_annot(a)       ->
        let p = Option.get "NONE" a.annot_payload in
        info "annot(%s, %s)" a.annot_tag p
    | Line_instr(i)       ->
        let comment = Option.get "NONE" i.instr_comment in
        info "instruction(%s, %s, %s, \"%s\", \"%s\")"
          (uint64_to_hex_string i.instr_addr) i.instr_opcode i.instr_revopcode
          i.instr_instr comment
  in
  List.iter print_line lines;
  info "======================";
  info "Fully processing file \"%s\"." input_file;
  let lines = parse input_file in
  info "==== parsed lines ====";
  let print_line l =
    info "%s:%i [%s]" l.dl_from_file l.dl_from_line l.dl_line_orig;
    info "  instr  => %s: %s/%s (%s)%s"
      l.dl_addr l.dl_opcode l.dl_revopcode l.dl_instr
      (Option.get "" (Option.map (fun s -> " // " ^ s) l.dl_comment));
    let print_constraint (line, orig, c) =
      info "  constr => %i (%s)" line orig;
      info "    -> [%s]\n" c
    in
    List.iter print_constraint l.dl_constrs
  in
  List.iter print_line lines;
  info "======================\n"
