(****************************************************************************)
(* BSD 2-Clause License                                                     *)
(*                                                                          *)
(* Copyright (c) 2019-2021 The Islaris Developers                           *)
(*                                                                          *)
(* Michael Sammler                                                          *)
(* Rodolphe Lepigre                                                         *)
(* Angus Hammond                                                            *)
(* Brian Campbell                                                           *)
(* Jean Pichon-Pharabod                                                     *)
(* Peter Sewell                                                             *)
(*                                                                          *)
(* All rights reserved.                                                     *)
(*                                                                          *)
(* This was in part funded from the European Research Council (ERC) under   *)
(* the European Union's Horizon 2020 research and innovation programme      *)
(* (grant agreement No 789108, "ELVER"), in part supported by the UK        *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), and in part funded by Google.           *)
(*                                                                          *)
(*                                                                          *)
(* Redistribution and use in source and binary forms, with or without       *)
(* modification, are permitted provided that the following conditions are   *)
(* met:                                                                     *)
(*                                                                          *)
(* 1. Redistributions of source code must retain the above copyright        *)
(* notice, this list of conditions and the following disclaimer.            *)
(*                                                                          *)
(* 2. Redistributions in binary form must reproduce the above copyright     *)
(* notice, this list of conditions and the following disclaimer in the      *)
(* documentation and/or other materials provided with the distribution.     *)
(*                                                                          *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        *)
(* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR    *)
(* A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT     *)
(* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   *)
(* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT         *)
(* LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,    *)
(* DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY    *)
(* THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT      *)
(* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE    *)
(* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.     *)
(*                                                                          *)
(*                                                                          *)
(* Exceptions to this license are detailed in THIRD_PARTY_FILES.md          *)
(****************************************************************************)

module Ast = Isla_lang.AST

type event = Ast.lrng Ast.event
type trace = Ast.lrng Ast.tree_trc
type maybe_fork = Ast.lrng Ast.maybe_fork

(** [filter_events pred trs] returns a copy of [trs] in which only events that
    satisfy the predicate [pred] have been kept. *)
let rec filter_events : (int -> event -> bool) -> trace -> trace = fun pred tr ->
  let Ast.TreeTrace(es, mf) = tr in
  let mf =
    match mf with
    | Ast.Cases(n, trs) -> Ast.Cases(n, List.map (filter_events pred) trs)
    | Ast.End           -> Ast.End
  in
  Ast.TreeTrace(List.filteri pred es, mf)

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
      let ast = P.tree_trc_start L.token lexbuf in
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
