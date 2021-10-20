# Linking isla-coq proofs to the Sail generated Coq model

This directory contains some infrastructure to connect isla-coq to the
Coq model generated from the RISC-V Sail model.

## Installation
One can install the Sail model with the following steps:
```
git clone https://github.com/mit-plv/bbv.git
cd bbv
make
make install
cd ..

wget https://github.com/riscv/sail-riscv/archive/9f71c756484a4aac7c211d5ea266f45b0b3942e7.tar.gz -O sail.tar.gz
tar xvf sail.tar.gz
mv sail-riscv-*/prover_snapshots/coq coq
rm -r sail-riscv-*/
cd coq
# Adjust the end of build as follows:
# cd ../../RV32
# coqc $BBV_OPT -Q . RV32 -Q ../lib/sail Sail riscv_extras.v
# coqc $BBV_OPT -Q . RV32 -Q ../lib/sail Sail mem_metadata.v
# coqc $BBV_OPT -Q . RV32 -Q ../lib/sail Sail riscv_types.v
# coqc $BBV_OPT -Q . RV32 -Q ../lib/sail Sail riscv.v
# cd ../RV64
# coqc $BBV_OPT -Q . RV64 -Q ../lib/sail Sail riscv_extras.v
# coqc $BBV_OPT -Q . RV64 -Q ../lib/sail Sail mem_metadata.v
# coqc $BBV_OPT -Q . RV64 -Q ../lib/sail Sail riscv_types.v
# coqc $BBV_OPT -Q . RV64 -Q ../lib/sail Sail riscv.v
# cd ../duopod
# coqc $BBV_OPT -Q . RVduopod -Q ../lib/sail Sail riscv_extras.v
# coqc $BBV_OPT -Q . RVduopod -Q ../lib/sail Sail mem_metadata.v
# coqc $BBV_OPT -Q . RVduopod -Q ../lib/sail Sail riscv_duopod_types.v
# coqc $BBV_OPT -Q . RVduopod -Q ../lib/sail Sail riscv_duopod.v

# Adjust riscv.v for RV32, RV64 and duopod to use "Require Import {RV32/RV64/RVduopod}.riscv_types."
# instead of "Require Import riscv_types." The same for mem_metadata and riscv_extras.

# Adjust riscv_extras.v for RV32, RV64 and duopod to import "Require Import Lia."

sed -i s/omega/lia/ RV32/riscv_extras.v
sed -i s/omega/lia/ RV64/riscv_extras.v
sed -i s/omega/lia/ duopod/riscv_extras.v

./build
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Sail" lib/sail/*.{v,vo}
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RV32" RV32/*.{v,vo}
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RV64" RV64/*.{v,vo}
install -m a+rw -D -t "$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/RVduopod" duopod/*.{v,vo}
ln -s _dune dune
```
