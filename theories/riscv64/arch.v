Require Import isla.lifting.

Global Instance riscv64_arch : Arch := {|
  arch_pc_reg := "PC";
|}.