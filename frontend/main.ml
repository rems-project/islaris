open Cmdliner
open Isla_lang_if
open Version
open Extra

(** Options required in [Isla] mode. *)
type isla_config = {
  def_name    : string; (** Name for the definiton of the traces in Coq. *)
  output_file : string option; (** Path to the output file. *)
}

let default_def_name : string = "trace"

(** Options required in [Dump] mode. *)
type dump_config = {
  name_template : Template.t; (** File and definition name template. *)
  output_dir : string; (** Directory where to write the generated files. *)
  coq_prefix : string list; (** Coq module path prefix for generated files. *)
  nb_jobs : int; (** Max number of threads to run in parallel. *)
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
let run_dump : dump_config -> string -> unit = fun cfg ->
  Decomp.run cfg.name_template cfg.output_dir cfg.coq_prefix cfg.nb_jobs

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

(** [is_valid_coq_ident s] indicates whether [s] is a valid Coq identifier. An
    identifier that is valid in this sense can be used everywhere: as the name
    of a Coq definition, or as a Coq module path member, for example. *)
let is_valid_coq_ident : string -> bool = fun s ->
  let valid_char first c =
    match c with
    | 'a'..'z' | 'A'..'Z' -> true
    | '0'..'9' | '_'      -> not first
    | _                   -> false
  in
  String.length s <> 0 &&
  valid_char true s.[0] &&
  String.for_all (valid_char false) s

let default_coq_dir : string -> string list = fun base ->
  ["isla"; "examples"; base]

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
    let keys_descr =
      let key_descr (k, d) = Printf.sprintf "\"{%s}\" (%s)" k d in
      String.concat ", " (List.map key_descr Decomp.template_keys)
    in
    Printf.sprintf "Specifies a $(docv) for the produced Coq definition \
      holding the traces. In Isla mode, the default name is \"%s\". In Dump \
      mode, $(docv) plays the role of a template used to generate Coq \
      definition names and file names. It should contain at least one of the \
      following strings (that are substituted with the described value): %s. \
      The default value for the template is \"%s\"."
      default_def_name keys_descr Decomp.default_template
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

let coq_prefix =
  let doc =
    Printf.sprintf "Specify the logical Coq directory (i.e., module path) \
      under which the generated files are placed. This option is only valid \
      in Dump mode. The argument $(docv) is expected to be a dot-sperated \
      list of identifiers formed of letters, underscores, and numbers (with \
      a letter in first position). If no explicit Coq directory is given \
      then it defaults to \"%s\", where BASE is the base name of the input \
      file. If BASE is not a valid identifier then the command fails."
      (String.concat "." (default_coq_dir "BASE"))
  in
  let coqdir =
    let parse s =
      let ids = String.split_on_char '.' s in
      if ids <> [""] && List.for_all is_valid_coq_ident ids then Ok(ids) else
      Error(`Msg "invalid COQDIR argument")
    in
    let pp fmt ids = Format.pp_print_string fmt (String.concat "." ids) in
    Arg.conv ~docv:"COQDIR" (parse, pp)
  in
  let i = Arg.(info ["coqdir"] ~docv:"COQDIR" ~doc) in
  Arg.(value & opt (some coqdir) None & i)

let j =
  let doc =
    "Specify a maximum $(docv) of jobs to run in parallel. This is only \
     useful in Dump mode."
  in
  let i = Arg.(info ["j"; "jobs"] ~docv:"JOBS" ~doc) in
  Arg.(value & opt int 1 & i)

let input_file =
  let doc =
    "Isla language source file or annotated object dump file. If no running \
     mode is specified, then the extension is used to determine the relevant \
     mode (\".isla\" for Isla mode, and \".dump\" for Dump mode)."
  in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let opts_config : config Term.t =
  let build_isla_config output def_name input_file =
    let def_name =
      let def_name = Option.get default_def_name def_name in
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
  let build_dump_config output def_name coq_prefix j input_file =
    let name_template =
      let def_name = Option.get Decomp.default_template def_name in
      let keys =
        let fn acc (k, _) = SSet.add k acc in
        List.fold_left fn SSet.empty Decomp.template_keys
      in
      let template =
        try Template.make keys def_name with Invalid_argument(msg) ->
          panic "Invalid name template \"%s\": %s." def_name msg
      in
      (* Check that the template is well-formed. *)
      if SSet.is_empty (Template.used_keys template) then
        panic "Invalid name template \"%s\": no key used." def_name;
      let worst_example =
        let m = SSet.fold (fun e acc -> SMap.add e "0" acc) keys SMap.empty in
        try Template.subst template m with Invalid_argument(_) ->
          assert false (* Unreachable. *)
      in
      if not (is_valid_coq_ident worst_example) then
        panic "Invalid name template \"%s\": may lead to an invalid Coq path \
          member." def_name;
      template
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
    let coq_prefix =
      match coq_prefix with
      | Some(p) -> p
      | None    ->
      let base = Filename.chop_extension (Filename.basename input_file) in
      if not (is_valid_coq_ident base) then
        panic "A coq directory name cannot be derived from the name of the \
          input file, use the --coqdir option.";
      default_coq_dir base
    in
    {name_template; output_dir; coq_prefix; nb_jobs = j}
  in
  let build output def_name mode_flag coq_prefix j input_file =
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
      | Isla_mode when coq_prefix = None ->
          Isla(build_isla_config output def_name input_file)
      | Isla_mode                        ->
          panic "Option --coqdir is only available in Dump mode.";
      | Dump_mode                        ->
          Dump(build_dump_config output def_name coq_prefix j input_file)
    in
    {input_file; mode}
  in
  let open Term in
  pure build $ output $ def_name $ mode_flag $ coq_prefix $ j $ input_file

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
