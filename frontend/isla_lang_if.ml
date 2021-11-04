module Ast = Isla_lang.AST

type event = Ast.lrng Ast.event
type trace = Ast.lrng Ast.forking_trc
type maybe_fork = Ast.lrng Ast.maybe_fork

(** [filter_events pred trs] returns a copy of [trs] in which only events that
    satisfy the predicate [pred] have been kept. *)
let filter_events : (event -> bool) -> trace -> trace = fun pred trs ->
  let open Ast in
  let rec filter_trace (ForkingTrace(trs, mf)) =
    ForkingTrace(List.filter pred trs, filter_maybe_fork mf)
  and filter_maybe_fork mf =
    match mf with
    | Fork(n, trcs) -> Fork(n, List.map filter_trace trcs)
    | NoFork    -> NoFork
  in
  filter_trace trs

module Parser = struct
  exception Parse_error of string

  let parse_file : string -> trace = fun fname ->
    let module L = Isla_lang.Lexer in
    let module P = Isla_lang.Parser in
    let fail fmt =
      let k _ = raise (Parse_error(Format.flush_str_formatter ())) in
      Format.kfprintf k Format.str_formatter fmt
    in
    let loc_pp ff loc =
      let open Lexing in
      Format.fprintf ff "%s %i:%i" loc.pos_fname loc.pos_lnum (loc.pos_cnum - loc.pos_bol)
    in
    let range_pp ff (loc_start, loc_end) =
      let open Lexing in
      Format.fprintf ff "%a-%i:%i" loc_pp loc_start
        loc_end.pos_lnum (loc_end.pos_cnum - loc_end.pos_bol)
    in
    let ic = try open_in fname with Sys_error(msg) -> fail "%s" msg in
    let lexbuf = Lexing.from_channel ic in
    try
      let ast = P.forking_trc_start L.token lexbuf in
      close_in ic;
      ast
    with e ->
    close_in ic;
    match e with
    | L.Error(msg) ->
        let loc = Lexing.lexeme_start_p lexbuf in
        fail "Lexing error as [%a]: %s." loc_pp loc msg
    | P.Error      ->
        let loc_start = Lexing.lexeme_start_p lexbuf in
        let loc_end   = Lexing.lexeme_end_p   lexbuf in
        fail "Parse error at [%a]." range_pp (loc_start, loc_end)
    | e            ->
        fail "Unexpected exception: %s." (Printexc.to_string e)
end
