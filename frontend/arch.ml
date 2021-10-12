open Extra

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

type t = arch

let aarch64 : arch = {
  arch_ignored_regs  = [
    "SEE";
    "BTypeNext";
    "__currentInstrLength";
    "__PC_changed";
    "__unconditional";
    "__v81_implemented";
    "__v82_implemented";
    "__v83_implemented";
    "__v84_implemented";
    "__v85_implemented";
    "__trickbox_enabled";
    "__CNTControlBase";
    "__defaultRAM";
    "__isla_monomorphize_reads";
    "__isla_monomorphize_writes";
    "__highest_el_aarch32";
  ];
  arch_isla_config   = Filename.concat Config.etc "aarch64_isla_coq.toml";
  arch_snapshot_file = "aarch64-pc.ir";
  arch_coq_name      = "aarch64";
}

let riscv64 : arch = {
  arch_ignored_regs  = [ "nextPC"; ];
  arch_isla_config   = Filename.concat Config.etc "riscv64_isla_coq.toml";
  arch_snapshot_file = "riscv64.ir";
  arch_coq_name      = "riscv64";
}

let supported_archs : (string * arch) list =
  [ ("aarch64", aarch64) ; ("riscv64", riscv64) ]

let arch_list : string list =
  List.map fst supported_archs

let find_arch : string -> arch = fun key ->
  List.assoc key supported_archs
