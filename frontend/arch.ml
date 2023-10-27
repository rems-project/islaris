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
    "__monomorphize_reads";
    "__monomorphize_writes";
    "__isla_vector_gpr";
    "__highest_el_aarch32";
  ];
  arch_isla_config   = Filename.concat Config.etc "aarch64_isla_coq.toml";
  arch_snapshot_file = "aarch64.ir";
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
