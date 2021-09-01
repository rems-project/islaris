open Cmdliner

module Of_decomp = struct
  let arg =
    let doc = "Annotated decompilation to process" in
    Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

  let cmd =
    let doc = "Process an annotated decompilation file to produce Coq definitions" in
    (Term.(pure Decomp.process_file $ arg), Term.info "of-decomp" ~doc)
end

(* This doesn't work as nicely as I expected, should probably be cleaned up at some point *)
let _ =
  Term.(exit @@ eval_choice Of_isla.cmd [Of_isla.cmd; Of_decomp.cmd])
