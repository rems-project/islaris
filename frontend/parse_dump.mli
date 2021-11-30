open Extra

(** Representation of an instruction specification. *)
type spec = {
  spec_imports  : string list;
  (** List of module paths to import for the specification. *)
  spec_spec     : string;
  (** The specification itself. *)
  spec_tactics  : string list;
  (** A list of tactics to use, in order. *)
  spec_admitted : bool;
  (** Should the specification be admitted? *)
}

(** Representation of an annotated, decompiled instruction. *)
type decomp_line = {
  dl_from_file  : Filename.filepath;
  (** Path to the file from which the instruction comes from. *)
  dl_from_line  : int;
  (** Line number for the instruction in the file. *)
  dl_line_orig  : string;
  (** Full (original) instruction line from the file. *)
  dl_addr       : string;
  (** Address of the instruction. *)
  dl_real_addr  : string;
  (** Real address of the instruction (using provided base address). *)
  dl_opcode     : string;
  (** Instruction opcode. *)
  dl_revopcode  : string;
  (** Reversed instruction opcode (other endianness). *)
  dl_constrs    : (int * string * string) list;
  (** Annotated constraints (line number, original line, the constraint). *)
  dl_instr      : string;
  (** Instruction. *)
  dl_comment    : string option;
  (** Possible comment. *)
  dl_spec       : spec option;
  (** Possible specification. *)
  dl_linearize  : string list;
  (** Functions Isla shoud linearize. *)
  dl_isla_cfg   : string option;
  (** Potential non-default Isla configuration file name to use. *)
  dl_parametric : string option;
  (** --partial flag to pass to isla. *)
}

(** [parse input_file] parses file [input_file] to obtain a list of annotated,
    decompiled instructions. *)
val parse : Filename.filepath -> decomp_line list

(** [parse_and_pp_debug oc input_file] parses file [input_file] and then print
    various debugging information for the parser. *)
val parse_and_pp_debug : out_channel -> Filename.filepath -> unit
