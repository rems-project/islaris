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

(** Standard library extension (mostly). *)

type 'a eq = 'a -> 'a -> bool

module Format = struct
  include Format

  (** Short name for the type of a pretty-printing function. *)
  type 'a pp = Format.formatter -> 'a -> unit

  (** Short name for a standard formatter. *)
  type 'a outfmt = ('a, formatter, unit) format

  (** Short name for a standard formatter with continuation. *)
  type ('a, 'b) koutfmt = ('a, formatter, unit, unit, unit, 'b) format6

  let write_file : string -> (formatter -> unit) -> unit = fun fname pp ->
    let oc = open_out fname in
    let ff = formatter_of_out_channel oc in
    pp ff; print_flush (); close_out oc
end

module String = struct
  include String

  let for_all : (char -> bool) -> string -> bool = fun pred s ->
    let exception Bad_char in
    let check_pred c = if not (pred c) then raise Bad_char in
    try String.iter check_pred s; true with Bad_char -> false

  (** [chop size s] chops string [s] into chunks of size [size] (in order). If
      the length of [s] is not a multiple of [size] then [Invalid_argument] is
      raise. *)
  let chop : int -> string -> string list = fun size s ->
    if String.length s mod size <> 0 then
      invalid_arg "String.chop: bad chunk size";
    let fn i = String.sub s (i * size) size in
    List.init (String.length s / size) fn
end

module Option = struct
  type 'a t = 'a option

  let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
    match o with
    | None    -> None
    | Some(e) -> Some(f e)

  let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
    match o with
    | None    -> d
    | Some(e) -> f e

  let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
    match o with
    | None    -> ()
    | Some(e) -> f e

  let get : 'a -> 'a option -> 'a = fun d o ->
    match o with
    | None    -> d
    | Some(e) -> e

  let equal : 'a eq -> 'a option eq = fun eq o1 o2 ->
    match (o1, o2) with
    | (None    , None    ) -> true
    | (Some(e1), Some(e2)) -> eq e1 e2
    | (_       , _       ) -> false

  let pp : 'a Format.pp -> 'a option Format.pp = fun pp_elt oc o ->
    match o with
    | None   -> ()
    | Some e -> pp_elt oc e
end

(** Basic format transformer to add to console output. *)
module Color = struct
  let with_color k fmt = "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"

  let red fmt = with_color "31" fmt
  let gre fmt = with_color "32" fmt
  let yel fmt = with_color "33" fmt
  let blu fmt = with_color "34" fmt
  let mag fmt = with_color "35" fmt
  let cya fmt = with_color "36" fmt
end

(** [wrn fmt] outputs a waning to [stderr] using [Format] format [fmt] and the
correponding arguments. A newline character is automatically printed after the
message (which is shown in yellow), and [stderr] is flushed. *)
let wrn : 'a Format.outfmt -> 'a = fun fmt ->
  Format.eprintf (Color.yel (fmt ^^ "\n%!"))

(** [panic fmt] interrupts the program with [exit 1] after showing the message
given by the [Format] format [fmt]. A newline character is automatically added
at the end of the message (which is shown in red) and [stderr] is flushed. *)
let panic : ('a, 'b) Format.koutfmt -> 'a = fun fmt ->
  let fmt = Color.red (fmt ^^ "\n") in
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter fmt

module Filename =
  struct
    include Filename

    (** Type synonym representing a path to a file. *)
    type filepath = string

    (** Type synonym representing a path to a directory. *)
    type dirpath = string

    (** [realpath path] returns the absolute canonical path to file [path]. If
        [path] is invalid (i.e., it does not describe an existing file),  then
        the exception [Invalid_argument] is raised. *)
    external realpath : filepath -> filepath = "c_realpath"
  end

module Buffer = struct
  include Buffer

  let add_full_channel : t -> in_channel -> unit = fun buf ic ->
    try
      while true do
        add_char buf (input_char ic)
      done
    with End_of_file -> ()

  let add_file : t -> string -> unit = fun buf fname ->
    let ic = open_in fname in
    add_full_channel buf ic;
    close_in ic

  let from_file : string -> t = fun fname ->
    let buf = create 4096 in
    add_file buf fname; buf

  let to_file : string -> t -> unit = fun fname buf ->
    let oc = open_out fname in
    output_buffer oc buf;
    close_out oc
end

(** [read_file fname] returns the list of the lines of file [fname]. Note that
    the trailing newlines are removed. *)
let read_file : string -> string list = fun fname ->
  let ic = open_in fname in
  let lines = ref [] in
  try
    while true do lines := input_line ic :: !lines done;
    assert false (* Unreachable. *)
  with End_of_file -> close_in ic; List.rev !lines

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [invalid_arg fmt ...] raises [Invalid_argument] with the given message. It
    can be formed using the standard formatter syntax. *)
let invalid_arg : ('a, 'b) koutfmt -> 'a = fun fmt ->
  let cont _ = invalid_arg (Format.flush_str_formatter ()) in
  Format.kfprintf cont Format.str_formatter fmt

(** Sets of elements of [string] *)
module SSet = Set.Make(String)

(** Maps of [string] keys. *)
module SMap = Map.Make(String)

module Parallel = struct
  (** [iter j f tasks] concurrently calls function [f] on the elements of list
      [tasks], using [j] threads. Note that the function [f] receives as first
      argument a higher-order function [with_io_lock] which can be used to run
      its argument function after having acquired a lock protecting the output
      channels [stdout] and [stderr]. Note that function [with_io_lock] should
      always be called with an argument that terminates. In the case where [j]
      is strictly less than [1] then [Invalid_argument] is raised. *)
  let iter : int -> (int -> ((unit -> unit) -> unit) -> 'a -> unit) -> 'a list
      -> unit = fun j f tasks ->
    if j < 1 then invalid_arg "Parallel.iter";
    let io_mutex  = Mutex.create () in
    let bag_mutex = Mutex.create () in
    let bag = ref tasks in
    let rec thread_fun i =
      Mutex.lock bag_mutex;
      let task =
        match !bag with
        | t :: ts -> bag := ts; Mutex.unlock bag_mutex; t
        | []      -> Mutex.unlock bag_mutex; Thread.exit (); assert false
      in
      let with_io_loc protected_f =
        Mutex.lock io_mutex;
        try protected_f (); Mutex.unlock io_mutex with e ->
          Mutex.unlock io_mutex; raise e
      in
      f i with_io_loc task; thread_fun i
    in
    let ths = Array.init j (Thread.create thread_fun) in
    Array.iter Thread.join ths
end
