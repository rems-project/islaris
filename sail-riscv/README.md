# Installation

This is a work in progress directory trying to link isla to the Coq model generated from Sail.

One can install the Sail model with the following steps (NOT TESTED):
```
opam pin coq-bbv 1.2
wget https://github.com/rems-project/sail-arm/archive/4a5dd2c7be96f593c2853b80902aaddf083a3c24.tar.gz -O sail.tar.gz
tar xvf sail.tar.gz
mv sail-arm-*/arm-v8.5-a/snapshots/coq/ sail-coq
rm -r sail-arm-*/
cd sail-coq
< adjust build to pass the following flags to coqc: "-Q . aarch64 -Q lib Sail" >
< adjust aarch64.v to use "Require Import aarch64.aarch64_types." and "Require Import aarch64.aarch64_extras." >
./build
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RV32" RV32/*.{v,vo}
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RV64" RV64/*.{v,vo}
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RVduopod" RVduopod/*.{v,vo}
mkdir ../../_opam/lib/coq/user-contrib/Sail
cp lib/*.{v,vo} ../../_opam/lib/coq/user-contrib/Sail
mkdir ../../_opam/lib/coq/user-contrib/aarch64
cp *.{v,vo} ../../_opam/lib/coq/user-contrib/aarch64
ln -s _dune dune
```
