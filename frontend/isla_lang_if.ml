module Ast = Isla_lang.AST

type event = Ast.lrng Ast.event
type trace = Ast.lrng Ast.forking_trc
type maybe_fork = Ast.lrng Ast.maybe_fork

(** [filter_events pred trs] returns a copy of [trs] in which only events that
    satisfy the predicate [pred] have been kept. *)
let rec filter_events : (int -> event -> bool) -> trace -> trace = fun pred tr ->
  let Ast.ForkingTrace(es, mf) = tr in
  let mf =
    match mf with
    | Ast.Fork(n, trs) -> Ast.Fork(n, List.map (filter_events pred) trs)
    | Ast.NoFork       -> Ast.NoFork
  in
  Ast.ForkingTrace(List.filteri pred es, mf)

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
