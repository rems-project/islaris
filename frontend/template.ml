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
(* This research was supported in part by a European Research Council       *)
(* (ERC) Consolidator Grant for the project "RustBelt", funded under        *)
(* the European Union's Horizon 2020 Framework Programme (grant agreement   *)
(* no. 683289), in part by a European Research Council (ERC) Advanced       *)
(* Grant "ELVER" under the European Union's Horizon 2020 research and       *)
(* innovation programme (grant agreement no. 789108), in part by the UK     *)
(* Government Industrial Strategy Challenge Fund (ISCF) under the Digital   *)
(* Security by Design (DSbD) Programme, to deliver a DSbDtech enabled       *)
(* digital platform (grant 105694), in part by a Google PhD Fellowship      *)
(* (Sammler), in part by an EPSRC Doctoral Training studentship             *)
(* (Hammond), and in part by awards from Android Security's ASPIRE          *)
(* program and from Google Research.                                        *)
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
