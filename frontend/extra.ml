(** Standard library extension (mostly). *)

module Format = struct
  include Format

  (** Short name for the type of a pretty-printing function. *)
  type 'a pp = Format.formatter -> 'a -> unit

  (** Short name for a standard formatter. *)
  type 'a outfmt = ('a, formatter, unit) format

  (** Short name for a standard formatter with continuation. *)
  type ('a, 'b) koutfmt = ('a, formatter, unit, unit, unit, 'b) format6
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


