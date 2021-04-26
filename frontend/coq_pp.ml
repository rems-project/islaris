open Isla_lang
open Extra

let pp_event ff _ =
  let pp fmt = Format.fprintf ff fmt in
  pp "TODO"

(** [pp_trace_def name] is a pretty-printer for the Coq definition of a trace,
with given definition name [name]. *)
let pp_trace_def : string -> trace Format.pp = fun id ff (Trace(events)) ->
  let pp fmt = Format.fprintf ff fmt in
  pp "@[<v 2>Definition %s : trc := [" id;
  let print_event =
    let first = ref true in
    let print_event e =
      (if !first then first := false else pp ";");
      pp "@;%a" pp_event e
    in
    print_event
  in
  List.iter print_event events;
  pp ("@]" ^^ (if events = [] then "" else "@;") ^^ "].")

(** [pp_trace_file] is the entry point of the pretty-printer. *)
let pp_trace_file : trace Format.pp = fun ff tr ->
  let pp fmt = Format.fprintf ff fmt in
  pp "@[<v 0>From isla Require Import isla_lang.@;@;";
  pp "%a@]" (pp_trace_def "trace") tr

let write_trace : trace -> string -> unit = fun tr fname ->
  let buffer = Buffer.create 4096 in
  Format.fprintf (Format.formatter_of_buffer buffer) "%a@." pp_trace_file tr;
  (* Check if we should write the file (inexistent / contents different). *)
  let must_write =
    try Buffer.contents (Buffer.from_file fname) <> Buffer.contents buffer
    with Sys_error(_) -> true
  in
  if must_write then Buffer.to_file fname buffer
