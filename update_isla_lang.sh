#!/bin/bash

set -e

(cd ../isla-lang/ && eval $(opam env) && make)
cp ../isla-lang/_build/default/isla_lang.v theories/isla_lang.v
sed -i "/Require Import .*/d" theories/isla_lang.v
sed -i '3i\Require Export isla.base isla.bitvector.' theories/isla_lang.v
sed -i "s/  *$//" theories/isla_lang.v
