open Isla_lang
open Extra

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
  Format.fprintf ff "%i%%Z" i

let pp_register_name ff r =
  Format.fprintf ff "%S" r

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
      pp "(Ty_BitVec %i%%N)" n
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
  | Ast.Extract(i,j)  -> pp "Extract %i%%nat %i%%nat" i j
  | Ast.ZeroExtend(i) -> pp "ZeroExtend %i%%nat" i
  | Ast.SignExtend(i) -> pp "SignExtend %i%%nat" i

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

let rec pp_valu ff v =
  let pp fmt = Format.fprintf ff fmt in
  match v with
  | Ast.Val_Symbolic(i)  ->
      pp "Val_Symbolic %a" pp_var_name i
  | Ast.Val_Bool(b)      ->
      pp "Val_Bool %b" b
  | Ast.Val_I(i,j)       ->
      pp "Val_I %i%%Z %i%%Z" i j
  | Ast.Val_Bits(s)      ->
      pp "Val_Bits %S" s (* FIXME wrong type for s. *)
  | Ast.Val_Enum(e)      ->
      pp "Val_Enum %a" pp_enum e
  | Ast.Val_String(s)    ->
      pp "Val_String %S" s
  | Ast.Val_Unit         ->
      pp "Val_Unit"
  | Ast.Val_NamedUnit(r) ->
      pp "NamedUnit %a" pp_register_name r
  | Ast.Val_Vector(l)    ->
      pp "Val_Vector %a" (pp_list pp_valu) l
  | Ast.Val_List(l)      ->
      pp "Val_List %a" (pp_list pp_valu) l
  | Ast.Val_Struct(l)    ->
      let pp_elt ff (r, v) =
        Format.fprintf ff "(%a, %a)" pp_register_name r pp_valu v
      in
      pp "Val_Struct %a" (pp_list pp_elt) l
  | Ast.Val_Poison       ->
      pp "Val_Poison"

let rec pp_exp ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.Var(i,a)         ->
      pp "Val (%a) %a" pp_valu (Ast.Val_Symbolic i) pp_lrng a
  | Ast.Bits(bv,a)       ->
      pp "Val (%a) %a" pp_valu (Ast.Val_Bits(bv)) pp_lrng a
  | Ast.Bool(b,a)        ->
      pp "Val (%a) %a" pp_valu (Ast.Val_Bool(b)) pp_lrng a
  | Ast.Enum(e,a)        ->
      pp "Val (%a) %a" pp_valu (Ast.Val_Enum(e)) pp_lrng a
  | Ast.Unop(o,e,a)      ->
      pp "Unop %a (%a) %a" pp_unop o pp_exp e pp_lrng a
  | Ast.Binop(o,e1,e2,a) ->
      pp "Binop %a (%a) (%a) %a" pp_binop o pp_exp e1 pp_exp e2 pp_lrng a
  | Ast.Manyop(o,l,a)    ->
      pp "Manyop %a %a %a" pp_manyop o (pp_list pp_exp) l pp_lrng a
  | Ast.Ite(i,t,e,a)     ->
      pp "Ite (%a) (%a) (%a) %a" pp_exp i pp_exp t pp_exp e pp_lrng a

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
      pp "DefineEnum %i%%Z" i

let pp_event ff e =
  let pp fmt = Format.fprintf ff fmt in
  match e with
  | Ast.Smt(s,a)                   ->
      pp "Smt (%a) %a" pp_smt s pp_lrng a
  | Ast.Branch(i,s,a)              ->
      pp "Branch %i%%Z %S %a" i s pp_lrng a
  | Ast.ReadReg(r,l,v,a)           ->
      pp "ReadReg %a %a %a %a" pp_register_name r pp_accessor_list l
        pp_valu v pp_lrng a
  | Ast.WriteReg(r,l,v,a)          ->
      pp "WriteReg %a %a %a %a" pp_register_name r pp_accessor_list l
        pp_valu v pp_lrng a
  | Ast.ReadMem(v1,v2,v3,i,v,a)    ->
      pp "ReadMem (%a) (%a) (%a) %i%%Z %a %a" pp_valu v1 pp_valu v2 pp_valu v3
        i (pp_option (fun ff -> Format.fprintf ff "(%a)" pp_valu)) v pp_lrng a
  | Ast.WriteMem(i,v1,v2,v3,j,v,a) ->
      pp "WriteMem (%a) (%a) (%a) (%a) %i%%Z %a %a"
        pp_valu (Ast.Val_Symbolic(i)) pp_valu v1 pp_valu v2 pp_valu v3 j
        (pp_option (fun ff -> Format.fprintf ff "(%a)" pp_valu)) v pp_lrng a
  | Ast.BranchAddress(v,a)         ->
      pp "BranchAddress (%a) %a" pp_valu v pp_lrng a
  | Ast.Barrier(v,a)               ->
      pp "Barrier (%a) %a" pp_valu v pp_lrng a
  | Ast.CacheOp(v1,v2,a)           ->
      pp "CacheOp (%a) (%a) %a" pp_valu v1 pp_valu v2 pp_lrng a
  | Ast.MarkReg(s1,s2,a)           ->
      pp "MarkReg %S %S %a" s1 s2 pp_lrng a
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
