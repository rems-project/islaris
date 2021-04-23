#!/bin/bash

set -e

(cd ../isla-lang/ && eval $(opam env) && make)
cp ../isla-lang/_build/default/isla_lang.v theories/isla_lang.v
sed -i "s/Require Import .*.//" theories/isla_lang.v
sed -i '3i\Require Export isla.base isla.bitvector.' theories/isla_lang.v
