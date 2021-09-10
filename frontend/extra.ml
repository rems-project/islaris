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
