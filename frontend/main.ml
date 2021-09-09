open Cmdliner
open Isla_lang
open Version
open Extra

(** Options required in [Isla] mode. *)
type isla_config = {
  def_name    : string; (** Name for the definiton of the traces in Coq. *)
  output_file : string option; (** Path to the output file. *)
}

(** Options required in [Dump] mode. The function [file_name] is used to build
    the file name for a given instruction, given its address (first argument),
    and its opcode (second argument). *)
type dump_config = {
  file_name  : string -> string -> string; (** Definition name template. *)
  output_dir : string; (** Directory where to write the generated files. *)
}

(** Running mode. *)
type mode =
  | Isla of isla_config (** Translation of an Isla file. *)
  | Dump of dump_config (** Generation from an annotated object file dump. *)

(** Topl level configuration read form the command line. *)
type config = {
  input_file : string; (** Input file (Isla format or annotated dump). *)
  mode       : mode; (** Running mode. *)
}

(** [run_isla cfg input_file] runs the Isla mode on the file [input_file] with
    the configuration [cfg]. *)
let run_isla : isla_config -> string -> unit = fun cfg input_file ->
  let trs =
    try Parser.parse_file input_file with Parser.Parse_error(msg) ->
      panic "Error while parsing [%s]\n%s" input_file msg
  in
  Coq_pp.write_traces cfg.def_name trs cfg.output_file

(** [run_dump cfg input_file] runs the Dump mode on the file [input_file] with
    the configuration [cfg]. *)
let run_dump : dump_config -> string -> unit = fun cfg input_file ->
  Decomp.run cfg.file_name cfg.output_dir input_file

(** [run cfg] runs the program in the mode specified by [cfg]. Any error leads
    to the program being terminated cleanly. *)
let run : config -> unit = fun cfg ->
  try
    match cfg.mode with
    | Isla(isla_cfg) -> run_isla isla_cfg cfg.input_file
    | Dump(dump_cfg) -> run_dump dump_cfg cfg.input_file
  with e ->
    (* Just in case there is a bug somewhere. *)
    panic "Uncaught exception: [%s]." (Printexc.to_string e)

let output =
  let doc =
    "Write output to $(docv). In Isla mode $(docv) is expected to be either \
     a file name with \".v\" extension, \"-\" (in which case the output is \
     written to standard output), or a directory name (in which case the \
     output file is written to the directory, with a name constructed by \
     changing the extension of the input file. In Dump mode $(docv) should \
     give the path to a directory (it is created if it does not exist, but \
     not its parent directories)."
  in
  let i = Arg.(info ["o"; "output"] ~docv:"PATH" ~doc) in
  Arg.(value & opt (some string) None & i)

let def_name =
  let doc =
    "Specifies a $(docv) for the produced Coq definition holding the traces. \
     In Dump mode, at least one of the strings \"{addr}\" and \"{op}\" must \
     appear in the name to form a template. They are respectively replaced \
     by the address and opcode of the instruction in the input file. In Dump \
     mode, the given template is also used to generate file names."
  in
  let i = Arg.(info ["n"; "def-name"] ~docv:"NAME" ~doc) in
  Arg.(value & opt (some string) None & i)

type mode_name = Isla_mode | Dump_mode

let mode_flag =
  let isla_mode =
    let doc =
      "Run in Isla mode: the input file is expecte to be an Isla language \
       file, regardless of its extension."
    in
    (Some(Isla_mode), Arg.(info ["i"; "isla"] ~doc))
  in
  let dump_mode =
    let doc =
      "Run in Dump mode: the input file is expecte to be an annotated object \
       dump file, regardless of its extension."
    in
    (Some(Dump_mode), Arg.(info ["d"; "dump"] ~doc))
  in
  Arg.(value & vflag None [isla_mode; dump_mode])

let input_file =
  let doc =
    "Isla language source file or annotated object dump file. If no running \
     mode is specified, then the extension is used to determine the relevant \
     mode (\".isla\" for Isla mode, and \".dump\" for Dump mode)."
  in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let opts_config : config Term.t =
  let is_valid_coq_ident s =
    let valid_char first c =
      match c with
      | 'a'..'z' | 'A'..'Z' -> true
      | '0'..'9' | '_'      -> not first
      | _                   -> false
    in
    String.length s <> 0 &&
    valid_char true s.[0] &&
    String.for_all (valid_char false) s
  in
  let build_isla_config output def_name input_file =
    let def_name =
      let def_name = Option.get "trace" def_name in
      if is_valid_coq_ident def_name then def_name else
      panic "The name \"%s\" is not a valid Coq identifier." def_name
    in
    let output_file =
      match output with
      | None        ->
          (* Build output file name from input file. *)
          let dir = Filename.dirname input_file in
          let base = Filename.(remove_extension (basename input_file)) in
          let out_file = Filename.concat dir (base ^ ".v") in
          if is_valid_coq_ident base then Some(out_file) else
          panic "File name \"%s\", derived form the input file, leads to \
            an invalid Coq path member (\"%s\")." out_file base
      | Some("-"  ) -> None (* Output to [stdout]. *)
      | Some(fname) ->
      if Filename.extension fname = ".v" then
        (* We assume [fname] is a path to a Coq file: check it is valid. *)
        let dir = Filename.dirname fname in
        let _ =
          try
            if not (Sys.is_directory dir) then
              panic "Invalid path: \"%s\" is not a directory." dir
          with Sys_error(_) ->
            panic "Invalid path: directory \"%s\" does not exist." dir
        in
        let base = Filename.remove_extension (Filename.basename fname) in
        if is_valid_coq_ident base then Some(fname) else
        panic "File name \"%s\" leads to an invalid Coq path member (\"%s\")."
          fname base
      else
        (* Variable [fname] is a path to a directory. *)
        let _ =
          try
            if not (Sys.is_directory fname) then
              panic "Invalid path: \"%s\" is not a directory (nor a Coq \
                file)." fname
          with Sys_error(_) ->
            panic "Invalid path: directory \"%s\" does not exist." fname
        in
        let base = Filename.(remove_extension (basename input_file)) in
        if is_valid_coq_ident base then
          Some(Filename.concat fname (base ^ ".v"))
        else
          panic "File name \"%s\", derived form the input file, leads to \
            an invalid Coq path member (\"%s\")." (base ^ ".v") base
    in
    {def_name; output_file}
  in
  let build_dump_config output def_name input_file =
    let def_name =
      let fn def_name =
        let re = Str.regexp "[{][a-z]*[}]"in
        Str.full_split re def_name
      in
      Option.map fn def_name
    in
    let file_name addr opcode =
      match def_name with
      | None    -> "a" ^ addr
      | Some(l) ->
      let to_string elt =
        match elt with
        | Str.Text(s)         -> s
        | Str.Delim("{addr}") -> addr
        | Str.Delim("{op}"  ) -> opcode
        | Str.Delim(_       ) -> assert false (* unreachable *)
      in
      String.concat "" (List.map to_string l)
    in
    let _ =
      (* Check that [file_name] is well-formed. *)
      let template = file_name "{addr}" "{op}" in
      if template = file_name "" "" then
        panic "Invalid name template \"%s\": one of \"{addr}\" or \"{op}\" \
          must appear at least once." template;
      if not (is_valid_coq_ident (file_name "0" "1")) then
        panic "Invalid name template \"%s\": may lead to an invalid Coq path \
          member." template
    in
    let output_dir =
      match output with
      | None      -> Filename.dirname input_file
      | Some(dir) ->
      let dir_dir = Filename.dirname dir in
      let _ =
        try
          if not (Sys.is_directory dir_dir) then
            panic "Invalid path: \"%s\" is not a directory." dir_dir
        with Sys_error(_) ->
          panic "Invalid path: directory \"%s\" does not exist." dir_dir
      in
      let _ =
        try
          if not (Sys.is_directory dir) then
            panic "Invalid path: \"%s\" is not a directory." dir
        with Sys_error(_) ->
          Unix.mkdir dir 0o755
      in
      dir
    in
    {file_name; output_dir}
  in
  let build output def_name mode_flag input_file =
    let mode_name =
      match mode_flag with
      | Some(m) -> m
      | None    ->
      match Filename.extension input_file with
      | ".isla" -> Isla_mode
      | ".dump" -> Dump_mode
      | ""      -> panic "The input file \"%s\" has no extension, you must \
                     specify a mode with -i or -d." input_file
      | ext     -> panic "The input file \"%s\" has extension \"%s\", which \
                     is not recognised: specify a running mode with -i or -d."
                     input_file ext
    in
    let mode =
      match mode_name with
      | Isla_mode -> Isla(build_isla_config output def_name input_file)
      | Dump_mode -> Dump(build_dump_config output def_name input_file)
    in
    {input_file; mode}
  in
  Term.(pure build $ output $ def_name $ mode_flag $ input_file)

let cmd =
  let doc =
    "Converts traces generated by isla-footprint into Coq. Two modes are \
     available: Isla mode, used to process an Isla language file, and Dump \
     mode, used to process and annotated object dump file."
  in
  let exits =
    Term.exit_info ~doc:"on fatal errors." 1 ::
    Term.default_exits
  in
  (Term.(pure run $ opts_config), Term.info "isla-coq" ~doc ~exits ~version)

let _ =
  Term.(exit @@ eval cmd)
