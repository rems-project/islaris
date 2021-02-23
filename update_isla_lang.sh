#!/bin/bash

set -e

(cd ../isla-lang/ && eval $(opam env) && make)
cp ../isla-lang/_build/default/isla_lang.v theories/isla_lang.v
sed -i "s/Require Import Ott.ott_list_core./(* Require Import Ott.ott_list_core. *)/" theories/isla_lang.v
