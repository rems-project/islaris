open Extra

module SSet = Set.Make(String)
module SMap = Map.Make(String)

type decomp =
  | Text of string
  | Key of string

let decompose : string -> decomp list = fun s ->
  let fn sr =
    match sr with
    | Str.Text(s)  -> Text(s)
    | Str.Delim(d) -> Key(String.sub d 1 (String.length d - 2))
  in
  List.map fn (Str.full_split (Str.regexp "[{][a-z]*[}]") s)

type template = {
  template_string : string;
  template_decomp : decomp list;
  template_valid_keys : SSet.t;
  template_keys : SSet.t;
}

type t = template

let used_keys : t -> SSet.t = fun t ->
  t.template_keys

let make : SSet.t -> string -> t = fun template_valid_keys template_string ->
  let template_decomp = decompose template_string in
  let template_keys =
    let fn acc d = match d with Text(_) -> acc | Key(k)  -> SSet.add k acc in
    List.fold_left fn SSet.empty template_decomp
  in
  let check_key k =
    if not (SSet.mem k template_valid_keys) then
      invalid_arg "unknown key \"%s\"" k
  in
  SSet.iter check_key template_keys;
  {template_string; template_decomp; template_valid_keys; template_keys}

let compatible : SSet.t -> 'a SMap.t -> bool = fun s m ->
  SSet.for_all (fun k -> SMap.mem k m) s &&
  SMap.for_all (fun k _ -> SSet.mem k s) m

let subst : t -> string SMap.t -> string = fun t m ->
  if not (compatible t.template_valid_keys m) then
    invalid_arg "the provided map is incompatible with the template";
  let fn d = match d with Text(s) -> s | Key(k)  -> SMap.find k m in
  String.concat "" (List.map fn t.template_decomp)
