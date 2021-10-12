open Extra

(** Type of an architecture description. *)
type arch = {
  arch_ignored_regs  : string list;
  (** Registers for which read and write events are removed from traces. *)
  arch_isla_config   : Filename.filepath;
  (** Absolute path to the isla configuration file. *)
  arch_snapshot_file : string;
  (** Name of the snapshot file for this architecture. *)
  arch_coq_name      : string
  (** Name of Coq the module for this architecture. *)
}

(** Short synonym of [arch]. *)
type t = arch

(** [arch_list] gives the names of all available architecture. *)
val arch_list : string list

(** [find name] gives the description of the architecture of the given [name].
    If the [name] is unknown, the function raises [Not_found]. *)
val find_arch : string -> arch
