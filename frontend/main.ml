open Cmdliner
open Isla_lang
open Version
open Extra

type config = {
  input_file  : string;
  output_file : string;
}

let run : config -> unit = fun cfg ->
  let tr =
    try Parser.parse_file cfg.input_file with Parser.Parse_error(msg) ->
      panic "Error while parsing [%s]\n%s" cfg.input_file msg
  in
  Coq_pp.write_trace tr cfg.output_file

let output =
  let doc =
    "Write output to $(docv) instead of constructing the output file name \
     from the input file name (changing the extension to \".v\"."
  in
  let i = Arg.(info ["o"; "output"] ~docv:"FILE" ~doc) in
  Arg.(value & opt (some string) None & i)

let isla_file =
  let doc = "Isla language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let opts : config Term.t =
  let build input_file output =
    let output_file = Filename.remove_extension input_file ^ ".v" in
    { input_file; output_file }
  in
  Term.(pure build $ isla_file $ output)

let cmd =
  let doc = "Converts isla language files into Coq." in
  let exits =
    Term.exit_info ~doc:"on fatal errors." 1 ::
    Term.default_exits
  in
  (Term.(pure run $ opts), Term.info "isla-coq" ~doc ~exits ~version)

let _ =
  Term.(exit @@ eval cmd)
