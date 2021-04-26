module Ast = Isla_lang_ast

type trace = Ast.lrng Ast.trc

module Parser = struct
  exception Parse_error of string

  let parse_file : string -> trace = fun fname ->
    let module L = Isla_lang_lexer in
    let module P = Isla_lang_parser in
    let fail fmt =
      let k _ = raise (Parse_error(Format.flush_str_formatter ())) in
      Format.kfprintf k Format.str_formatter fmt
    in
    let loc_pp ff _ = Format.fprintf ff "..." in (* TODO *)
    let range_pp ff _ = Format.fprintf ff "..." in (* TODO *)
    let ic = try open_in fname with Sys_error(msg) -> fail "%s" msg in
    let lexbuf = Lexing.from_channel ic in
    try
      let ast = P.trc_start L.token lexbuf in
      close_in ic; ast
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
    | e       -> fail "Unexpected exception: %s." (Printexc.to_string e)
end
