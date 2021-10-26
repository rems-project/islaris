module Ast = Isla_lang.AST

type event = unit Ast.event
type trace = unit Ast.trc
type traces = unit Ast.trcs

(** [filter_events pred trs] returns a copy of [trs] in which only events that
    satisfy the predicate [pred] have been kept. *)
let filter_events : (event -> bool) -> traces -> traces = fun pred trs ->
  let open Ast in
  let filter_trace (Trace(tr)) = Trace(List.filter pred tr) in
  let filter_traces (Traces(trs)) = Traces(List.map filter_trace trs) in
  filter_traces trs

let erase_traces : 'a Ast.trcs -> traces =
  let open Ast in
  let rec erase_a_exp e =
    match e with
    | AExp_Val(v,_)       -> AExp_Val(v, ())
    | AExp_Unop(o,e,_)    -> AExp_Unop(o, erase_a_exp e, ())
    | AExp_Binop(o,x,y,_) -> AExp_Binop(o, erase_a_exp x,erase_a_exp y, ())
    | AExp_Manyop(o,es,_) -> AExp_Manyop(o, List.map erase_a_exp es, ())
    | AExp_Ite(x,y,z,_)   -> AExp_Ite(erase_a_exp x, erase_a_exp y,
                              erase_a_exp z, ())
  in
  let rec erase_exp e =
    match e with
    | Val(v,_)       -> Val(v, ())
    | Unop(o,e,_)    -> Unop(o, erase_exp e, ())
    | Binop(o,x,y,_) -> Binop(o, erase_exp x,erase_exp y, ())
    | Manyop(o,es,_) -> Manyop(o, List.map erase_exp es, ())
    | Ite(x,y,z,_)   -> Ite(erase_exp x, erase_exp y, erase_exp z, ())
  in
  let erase_smt s =
    match s with
    | DeclareConst(i,ty) -> DeclareConst(i, ty)
    | DefineConst(i,e)   -> DefineConst(i, erase_exp e)
    | Assert(e)          -> Assert(erase_exp e)
    | DefineEnum(i)      -> DefineEnum(i)
  in
  let erase_event e =
    match e with
    | Smt(s,_)                 -> Smt(erase_smt s, ())
    | Branch(i,s,_)            -> Branch(i, s, ())
    | ReadReg(s,l,v,_)         -> ReadReg(s, l, v, ())
    | WriteReg(s,l,v,_)        -> WriteReg(s, l, v, ())
    | ReadMem(a,b,c,i,vo,_)    -> ReadMem(a, b, c, i, vo, ())
    | WriteMem(a,b,c,d,i,vo,_) -> WriteMem(a, b, c, d, i, vo, ())
    | BranchAddress(v,_)       -> BranchAddress(v, ())
    | Barrier(v,_)             -> Barrier(v, ())
    | CacheOp(v,w,_)           -> CacheOp(v, w, ())
    | MarkReg(s,t,_)           -> MarkReg(s, t, ())
    | Cycle(_)                 -> Cycle(())
    | Instr(v,_)               -> Instr(v, ())
    | Sleeping(i,_)            -> Sleeping(i, ())
    | WakeRequest(_)           -> WakeRequest(())
    | SleepRequest(_)          -> SleepRequest(())
    | AssumeReg(s,l,v,_)       -> AssumeReg(s, l, v, ())
    | Assume(e,_)              -> Assume(erase_a_exp e, ())
  in
  let erase_trace (Trace es) = Trace (List.map erase_event es) in
  let erase_traces (Traces trs) = Traces (List.map erase_trace trs) in
  erase_traces

module Parser = struct
  exception Parse_error of string

  let parse_file : string -> traces = fun fname ->
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
      let ast = P.trcs_start L.token lexbuf in
      close_in ic; erase_traces ast
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

let compare : traces -> traces -> int =
  let open Ast in
  let rec erase_a_exp e =
    match e with
    | AExp_Val(v,_)       -> AExp_Val(v, ())
    | AExp_Unop(o,e,_)    -> AExp_Unop(o, erase_a_exp e, ())
    | AExp_Binop(o,x,y,_) -> AExp_Binop(o, erase_a_exp x,erase_a_exp y, ())
    | AExp_Manyop(o,es,_) -> AExp_Manyop(o, List.map erase_a_exp es, ())
    | AExp_Ite(x,y,z,_)   -> AExp_Ite(erase_a_exp x, erase_a_exp y,
                              erase_a_exp z, ())
  in
  let rec erase_exp e =
    match e with
    | Val(v,_)       -> Val(v, ())
    | Unop(o,e,_)    -> Unop(o, erase_exp e, ())
    | Binop(o,x,y,_) -> Binop(o, erase_exp x,erase_exp y, ())
    | Manyop(o,es,_) -> Manyop(o, List.map erase_exp es, ())
    | Ite(x,y,z,_)   -> Ite(erase_exp x, erase_exp y, erase_exp z, ())
  in
  let erase_smt s =
    match s with
    | DeclareConst(i,ty) -> DeclareConst(i, ty)
    | DefineConst(i,e)   -> DefineConst(i, erase_exp e)
    | Assert(e)          -> Assert(erase_exp e)
    | DefineEnum(i)      -> DefineEnum(i)
  in
  let erase_event e =
    match e with
    | Smt(s,_)                 -> Smt(erase_smt s, ())
    | Branch(i,s,_)            -> Branch(i, s, ())
    | ReadReg(s,l,v,_)         -> ReadReg(s, l, v, ())
    | WriteReg(s,l,v,_)        -> WriteReg(s, l, v, ())
    | ReadMem(a,b,c,i,vo,_)    -> ReadMem(a, b, c, i, vo, ())
    | WriteMem(a,b,c,d,i,vo,_) -> WriteMem(a, b, c, d, i, vo, ())
    | BranchAddress(v,_)       -> BranchAddress(v, ())
    | Barrier(v,_)             -> Barrier(v, ())
    | CacheOp(v,w,_)           -> CacheOp(v, w, ())
    | MarkReg(s,t,_)           -> MarkReg(s, t, ())
    | Cycle(_)                 -> Cycle(())
    | Instr(v,_)               -> Instr(v, ())
    | Sleeping(i,_)            -> Sleeping(i, ())
    | WakeRequest(_)           -> WakeRequest(())
    | SleepRequest(_)          -> SleepRequest(())
    | AssumeReg(s,l,v,_)       -> AssumeReg(s, l, v, ())
    | Assume(e,_)              -> Assume(erase_a_exp e, ())
  in
  let erase_trace (Trace es) = Trace (List.map erase_event es) in
  let erase_traces (Traces trs) = Traces (List.map erase_trace trs) in
  fun trs1 trs2 -> Stdlib.compare (erase_traces trs1) (erase_traces trs2)
