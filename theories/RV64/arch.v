Require Import isla.lifting.

Global Instance RV64_arch : Arch := {|
  arch_pc_reg := "PC";
|}.
