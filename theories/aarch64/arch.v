Require Import isla.lifting.

Global Instance aarch64_arch : Arch := {|
  arch_pc_reg := "_PC";
|}.
