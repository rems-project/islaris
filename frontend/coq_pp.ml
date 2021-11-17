open Isla_lang_if
open Extra

let pp_N ff i =
  assert (0 <= i);
  Format.fprintf ff "%i%%N" i

let pp_Z ff i =
  let (l, r) = if i < 0 then ("(", ")") else ("", "") in
  Format.fprintf ff "%s%i%s%%Z" l i r

let pp_str ff s =
  Format.fprintf ff "%S" (String.sub s 1 (String.length s - 2))

let pp_list pp_elt ff l =
  let pp fmt = Format.fprintf ff fmt in
  let first = ref true in
  let pp_elt ff e =
    pp "%s%a" (if !first then "" else "; ") pp_elt e;
    first := false
  in
  pp "["; List.iter (pp "%a" pp_elt) l; pp "]"

let pp_option pp_elt ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | None    -> pp "None"
  | Some(e) -> pp "(Some %a)" pp_elt e

let pp_lrng ff _ =
  Format.fprintf ff "Mk_annot"

let pp_var_name ff i =
  Format.fprintf ff "%a" pp_Z i

let pp_register_name ff r =
  Format.fprintf ff "%S" r

let remove_zeroes digits =
  let len = String.length digits in
  let rec first_non_zero i =
    if i < len && digits.[i] = '0' then first_non_zero (i+1) else i
  in
  let i = first_non_zero 0 in
  if i < len then String.sub digits i (len - i) else "0"

let bin_to_hex digits =
  let len = String.length digits in
  let digits = String.make (4 - len mod 4) '0' ^ digits in
  let build i =
    let binary = "0b" ^ String.sub digits (i * 4) 4 in
    let n = int_of_string binary in
    (Printf.sprintf "%x" n).[0]
  in
  String.init (String.length digits / 4) build

let pp_bv ff s =
  let pp fmt = Format.fprintf ff fmt in
  let (nb_bits, hex_digits) =
    try
      let len = String.length s in
      let digits = String.sub s 2 (len - 2) in
      match s.[1] with
      | 'b' -> (len - 2      , bin_to_hex digits)
      | 'x' -> (4 * (len - 2), digits           )
      | _   -> failwith "not a valid bitvector"
    with Invalid_argument(msg) | Failure(msg) ->
      panic "Error while converting bitvector %S: %s." s msg
  in
  pp "[BV{%a} 0x%s%%Z]" pp_N nb_bits (remove_zeroes hex_digits)

let pp_accessor ff a =
  let pp fmt = Format.fprintf ff fmt in
  match a with
  | Ast.Field(r) -> pp "Field %a" pp_register_name r

let pp_accessor_list ff l =
  pp_list pp_accessor ff (match l with Ast.Nil -> [] | Ast.Cons(l) -> l)

let pp_enum_id ff i =
  Format.fprintf ff "(Mk_enum_id %i%%nat)" i

let rec pp_ty ff ty =
  let pp fmt = Format.fprintf ff fmt in
  match ty with
  | Ast.Ty_Bool           ->
      pp "Ty_Bool"
  | Ast.Ty_BitVec(n)      ->
      pp "(Ty_BitVec %a)" pp_N n
  | Ast.Ty_Enum(i)        ->
      pp "(Ty_Enum %a)" pp_enum_id i
  | Ast.Ty_Array(ty1,ty2) ->
      pp "(Ty_Array %a %a)" pp_ty ty1 pp_ty ty2

let pp_unop ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.Not           -> pp "Not"
  | Ast.Bvnot         -> pp "Bvnot"
  | Ast.Bvredand      -> pp "Bvredand"
  | Ast.Bvredor       -> pp "Bvredor"
  | Ast.Bvneg         -> pp "Bvneg"
  | Ast.Extract(i,j)  -> pp "Extract %a %a" pp_N i pp_N j
  | Ast.ZeroExtend(i) -> pp "ZeroExtend %a" pp_N i
  | Ast.SignExtend(i) -> pp "SignExtend %a" pp_N i

let pp_bvarith ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.Bvnand  -> pp "Bvnand"
  | Ast.Bvnor   -> pp "Bvnor"
  | Ast.Bvxnor  -> pp "Bvxnor"
  | Ast.Bvsub   -> pp "Bvsub"
  | Ast.Bvudiv  -> pp "Bvudiv"
  | Ast.Bvudivi -> pp "Bvudivi"
  | Ast.Bvsdiv  -> pp "Bvsdiv"
  | Ast.Bvsdivi -> pp "Bvsdivi"
  | Ast.Bvurem  -> pp "Bvurem"
  | Ast.Bvsrem  -> pp "Bvsrem"
  | Ast.Bvsmod  -> pp "Bvsmod"
  | Ast.Bvshl   -> pp "Bvshl"
  | Ast.Bvlshr  -> pp "Bvlshr"
  | Ast.Bvashr  -> pp "Bvashr"

let pp_bvcomp ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.Bvult -> pp "Bvult"
  | Ast.Bvslt -> pp "Bvslt"
  | Ast.Bvule -> pp "Bvule"
  | Ast.Bvsle -> pp "Bvsle"
  | Ast.Bvuge -> pp "Bvuge"
  | Ast.Bvsge -> pp "Bvsge"
  | Ast.Bvugt -> pp "Bvugt"
  | Ast.Bvsgt -> pp "Bvsgt"

let pp_binop ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.Eq         -> pp "Eq"
  | Ast.Bvarith(o) -> pp "(Bvarith %a)" pp_bvarith o
  | Ast.Bvcomp(o)  -> pp "(Bvcomp %a)" pp_bvcomp o

let pp_bvmanyarith ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.Bvand -> pp "Bvand"
  | Ast.Bvor  -> pp "Bvor"
  | Ast.Bvxor -> pp "Bvxor"
  | Ast.Bvadd -> pp "Bvadd"
  | Ast.Bvmul -> pp "Bvmul"

let pp_manyop ff o =
  let pp fmt = Format.fprintf ff fmt in
  match o with
  | Ast.And            -> pp "And"
  | Ast.Or             -> pp "Or"
  | Ast.Bvmanyarith(o) -> pp "(Bvmanyarith %a)" pp_bvmanyarith o
  | Ast.Concat         -> pp "Concat"

let pp_enum_ctor ff n =
  Format.fprintf ff "Mk_enum_ctor %i%%nat" n

let pp_enum ff e =
  let pp fmt = Format.fprintf ff fmt in
  pp "(%a, %a)" pp_enum_id (fst e) pp_enum_ctor (snd e)

let pp_base_val ff v =
  let pp fmt = Format.fprintf ff fmt in
  match v with
  | Ast.Val_Symbolic(i)  ->
      pp "Val_Symbolic %a" pp_var_name i
  | Ast.Val_Bool(b)      ->
      pp "Val_Bool %b" b
  | Ast.Val_Bits(s)      ->
      pp "Val_Bits %a" pp_bv s
  | Ast.Val_Enum(e)      ->
      pp "Val_Enum %a" pp_enum e

let pp_assume_val ff v =
  let pp fmt = Format.fprintf ff fmt in
  match v with
  | Ast.AVal_Var(r,l)  ->
      pp "AVal_Var %a %a" pp_register_name r pp_accessor_list l
  | Ast.AVal_Bool(b)      ->
      pp "AVal_Bool %b" b
  | Ast.AVal_Bits(s)      ->
      pp "AVal_Bits %a" pp_bv s
  | Ast.AVal_Enum(e)      ->
      pp "AVal_Enum %a" pp_enum e

let rec pp_valu ff v =
  let pp fmt = Format.fprintf ff fmt in
  match v with
  | Ast.RegVal_Base(v')  ->
      pp "RegVal_Base (%a)" pp_base_val v'
  | Ast.RegVal_I(i,j)       ->
      pp "RegVal_I %a %a" pp_Z i pp_Z j
  | Ast.RegVal_String(s)    ->
      pp "RegVal_String %a" pp_str s
  | Ast.RegVal_Unit         ->
      pp "RegVal_Unit"
  | Ast.RegVal_NamedUnit(r) ->
      pp "NamedUnit %a" pp_register_name r
  | Ast.RegVal_Vector(l)    ->
      pp "RegVal_Vector %a" (pp_list pp_valu) l
  | Ast.RegVal_List(l)      ->
      pp "RegVal_List %a" (pp_list pp_valu) l
  | Ast.RegVal_Struct(l)    ->
      let pp_elt ff (r, v) =
        Format.fprintf ff "(%a, %a)" pp_register_name r pp_valu v
      in
      pp "RegVal_Struct %a" (pp_list pp_elt) l
  | Ast.RegVal_Poison       ->
      pp "RegVal_Poison"

let rec pp_exp ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.Val(v,a)         ->
      pp "Val (%a) %a" pp_base_val v pp_lrng a
  | Ast.Unop(o,e,a)      ->
      pp "Unop (%a) (%a) %a" pp_unop o pp_exp e pp_lrng a
  | Ast.Binop(o,e1,e2,a) ->
      pp "Binop (%a) (%a) (%a) %a" pp_binop o pp_exp e1 pp_exp e2 pp_lrng a
  | Ast.Manyop(o,l,a)    ->
      pp "Manyop %a %a %a" pp_manyop o (pp_list pp_exp) l pp_lrng a
  | Ast.Ite(i,t,e,a)     ->
      pp "Ite (%a) (%a) (%a) %a" pp_exp i pp_exp t pp_exp e pp_lrng a

let rec pp_a_exp ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.AExp_Val(v,a)         ->
      pp "AExp_Val (%a) %a" pp_assume_val v pp_lrng a
  | Ast.AExp_Unop(o,e,a)      ->
      pp "AExp_Unop (%a) (%a) %a" pp_unop o pp_a_exp e pp_lrng a
  | Ast.AExp_Binop(o,e1,e2,a) ->
      pp "AExp_Binop (%a) (%a) (%a) %a" pp_binop o
        pp_a_exp e1 pp_a_exp e2 pp_lrng a
  | Ast.AExp_Manyop(o,l,a)    ->
      pp "AExp_Manyop %a %a %a" pp_manyop o (pp_list pp_a_exp) l pp_lrng a
  | Ast.AExp_Ite(i,t,e,a)     ->
      pp "AExp_Ite (%a) (%a) (%a) %a"
        pp_a_exp i pp_a_exp t pp_a_exp e pp_lrng a

let pp_smt ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.DeclareConst(i,ty) ->
      pp "DeclareConst %a %a" pp_var_name i pp_ty ty
  | Ast.DefineConst(i,e)   ->
      pp "DefineConst %a (%a)" pp_var_name i pp_exp e
  | Ast.Assert(e)          ->
      pp "Assert (%a)" pp_exp e
  | Ast.DefineEnum(i)      ->
      pp "DefineEnum %a" pp_Z i

let pp_event ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.Smt(s,a)                   ->
      pp "Smt (%a) %a" pp_smt s pp_lrng a
  | Ast.Branch(i,s,a)              ->
      pp "Branch %a %a %a" pp_Z i pp_str s pp_lrng a
  | Ast.ReadReg(r,l,v,a)           ->
      pp "ReadReg %a %a (%a) %a" pp_register_name r pp_accessor_list l
        pp_valu v pp_lrng a
  | Ast.WriteReg(r,l,v,a)          ->
      pp "WriteReg %a %a (%a) %a" pp_register_name r pp_accessor_list l
        pp_valu v pp_lrng a
  | Ast.ReadMem(v1,v2,v3,i,v,a)    ->
      pp "ReadMem (%a) (%a) (%a) %a %a %a"
        pp_valu v1 pp_valu v2 pp_valu v3 pp_N i
        (pp_option (fun ff -> Format.fprintf ff "(%a)" pp_valu)) v pp_lrng a
  | Ast.WriteMem(i,v1,v2,v3,j,v,a) ->
      pp "WriteMem (%a) (%a) (%a) (%a) %a %a %a"
        pp_valu i pp_valu v1 pp_valu v2 pp_valu v3 pp_N j
        (pp_option (fun ff -> Format.fprintf ff "(%a)" pp_valu)) v pp_lrng a
  | Ast.BranchAddress(v,a)         ->
      pp "BranchAddress (%a) %a" pp_valu v pp_lrng a
  | Ast.Barrier(v,a)               ->
      pp "Barrier (%a) %a" pp_valu v pp_lrng a
  | Ast.CacheOp(v1,v2,a)           ->
      pp "CacheOp (%a) (%a) %a" pp_valu v1 pp_valu v2 pp_lrng a
  | Ast.MarkReg(s1,s2,a)           ->
      pp "MarkReg %S %a %a" s1 pp_str s2 pp_lrng a
  | Ast.Cycle(a)                   ->
      pp "Cycle %a" pp_lrng a
  | Ast.Instr(v,a)                 ->
      pp "Instr (%a) %a" pp_valu v pp_lrng a
  | Ast.Sleeping(i,a)              ->
      pp "Sleeping %a %a" pp_var_name i pp_lrng a
  | Ast.WakeRequest(a)             ->
      pp "WakeRequest %a" pp_lrng a
  | Ast.SleepRequest(a)            ->
      pp "SleepRequest %a" pp_lrng a
  | Ast.AssumeReg(r,l,v,a)         ->
      pp "AssumeReg %a %a (%a) %a" pp_register_name r pp_accessor_list l
        pp_valu v pp_lrng a
  | Ast.Assume(e,a)               ->
      pp "Assume (%a) %a" pp_a_exp e pp_lrng a

(** [pp_trace_def name] is a pretty-printer for the Coq definition of a trace,
with given definition name [name]. *)
let pp_events : event list Format.pp = fun ff events ->
  let pp fmt = Format.fprintf ff fmt in
  let print_event e =
    pp "@;%a :t:" pp_event e
  in
  List.iter print_event events

let rec pp_tree_trace : trace Format.pp = fun ff tr ->
  let TreeTrace(trcs, cont) = tr in
  let pp fmt = Format.fprintf ff fmt in
  pp "%a" pp_events trcs;
  pp "%a" pp_maybe_fork cont

and pp_maybe_fork : maybe_fork Format.pp = fun ff mf ->
  let pp fmt = Format.fprintf ff fmt in
  match mf with
  | Ast.Cases(n, trcs) ->
     pp "@;@[<v 2>tcases [";
     let print_trace =
       let first = ref true in
       let print_trace e =
         (if !first then first := false else pp ";");
         pp "%a" pp_tree_trace e
       in
       print_trace
     in
     List.iter print_trace trcs;
     pp "@]@;]"
  | Ast.End        -> pp "@;tnil"

let pp_trace_def : string -> trace Format.pp = fun id ff trc ->
  let pp fmt = Format.fprintf ff fmt in
  pp "@[<v 2>Definition %s : isla_trace :=" id;
  pp "%a" pp_tree_trace trc;
  pp "@]@;."

(** [pp_trace_file name] is the entry point of the pretty-printer. A [name] is
provided as argument: it is used for the generated Coq "Definition". *)
let pp_trace_file : string -> trace Format.pp = fun id ff tr ->
  let pp fmt = Format.fprintf ff fmt in
  pp "@[<v 0>From isla Require Import opsem.@;@;";
  pp "%a@]" (pp_trace_def id) tr

let write_trace_to_file : string -> trace -> string -> unit =
    fun id tr fname ->
  let buffer = Buffer.create 4096 in
  let fmt = Format.formatter_of_buffer buffer in
  Format.fprintf fmt "%a@." (pp_trace_file id) tr;
  (* Check if we should write the file (inexistent / contents different). *)
  let must_write =
    try Buffer.contents (Buffer.from_file fname) <> Buffer.contents buffer
    with Sys_error(_) -> true
  in
  if must_write then Buffer.to_file fname buffer

let write_trace : string -> trace -> string option -> unit =
    fun id tr fname ->
  match fname with
  | Some(fname) -> write_trace_to_file id tr fname
  | None        -> Format.printf "%a@." (pp_trace_file id) tr
