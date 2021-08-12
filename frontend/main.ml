open Cmdliner
open Isla_lang
open Version
open Extra

type config = {
  input_file      : string;
  output_file     : string option;
  definition_name : string;
}

let run : config -> unit = fun cfg ->
  let trs =
    try Parser.parse_file cfg.input_file with Parser.Parse_error(msg) ->
      panic "Error while parsing [%s]\n%s" cfg.input_file msg
  in
  Coq_pp.write_traces cfg.definition_name trs cfg.output_file

let output =
  let doc =
    "Write output to $(docv) instead of constructing the output file name \
     from the input file name (changing the extension to \".v\"."
  in
  let i = Arg.(info ["o"; "output"] ~docv:"FILE" ~doc) in
  Arg.(value & opt (some string) None & i)

let definition_name =
  let doc =
    "Generate a definition with name $(docv)."
  in
  let i = Arg.(info ["definition-name"] ~docv:"NAME" ~doc) in
  Arg.(value & opt (some string) None & i)

let isla_file =
  let doc = "Isla language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let opts : config Term.t =
  let build input_file output def_name =
    let output_file =
      match output with
      | Some("-"  ) -> None
      | Some(fname) -> Some(fname)
      | None        -> Some(Filename.remove_extension input_file ^ ".v")
    in
    let definition_name =
      match def_name with
      | Some(def) -> def
      | None        -> "trace"
    in
    { input_file; output_file; definition_name }
  in
  Term.(pure build $ isla_file $ output $ definition_name)

let cmd =
  let doc = "Converts isla language files into Coq." in
  let exits =
    Term.exit_info ~doc:"on fatal errors." 1 ::
    Term.default_exits
  in
  (Term.(pure run $ opts), Term.info "isla-coq" ~doc ~exits ~version)

let _ =
  Term.(exit @@ eval cmd)
