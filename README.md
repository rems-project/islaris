# Islaris: verification of machine code against authoritative ISA semantics

## Setup

It is recommended to install the dependencies of Islaris via opam
(version 2.0.0 or newer) into a new switch. This can be done via the
following commands. You also need to make sure that you have the GNU
GMP library on your system (`libgmp-dev` package on Debian),
aarch64-linux-gnu-as (`binutils-aarch64-linux-gnu` package on Debian,
`aarch64-elf-binutils` package on MacOS) and
riscv64-linux-gnu-as (`binutils-riscv64-linux-gnu` package on Debian, `riscv64-elf-binutils` on MacOS).

```
opam switch create . ocaml-variants.4.14.0+options ocaml-option-flambda --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
make builddep
```

You might need to run `eval $(opam env)` afterwards to update the environment of your shell.

The Islaris frontend also requires cloning and setting up Isla ( https://github.com/rems-project/isla )
and Isla snapshots ( https://github.com/rems-project/isla-snapshots ) in a directory next to
the Islaris repository:
```
cd ..
git clone https://github.com/rems-project/isla.git
git clone https://github.com/rems-project/isla-snapshots.git
# Follow the instructions in https://github.com/rems-project/isla/blob/master/README.md to setup Isla
```
(Alternatively, one can also set the "ISLA_REPO" and "ISLA_SNAP_REPO" environment variables
to point to a working checkout of Isla resp. Isla snapshots.)

The following commits of isla and isla-snapshots are tested:
```
isla: b8e614bda4a20e42c37d8b216853653133d04322
isla-snapshots: b58da9170470a422c9396983ac8f87f0a63ba6f8
```

Once all needed libraries have been installed, Islaris can be built by running `make` from its root directory.

## Generating Coq traces from a partial decompilation of pkvm

Currently, one needs to manually instrument the output of `objdump` so that it
contains only the relevant code.

For example, we can start from the following segment of `objdump` output taken
from an exception handler in pkvm:
```
    7400:	a9bf07e0 	stp	x0, x1, [sp, #-16]!
    7404:	d53c5200 	mrs	x0, esr_el2
    7408:	d35afc00 	lsr	x0, x0, #26
    740c:	f100581f 	cmp	x0, #0x16
    7410:	54ff9f81 	b.ne	6800 <__host_exit>  // b.any
    7414:	a94007e0 	ldp	x0, x1, [sp]
    7418:	f1000c1f 	cmp	x0, #0x3
    741c:	54ff9f22 	b.cs	6800 <__host_exit>  // b.hs, b.nlast
    7420:	910043ff 	add	sp, sp, #0x10
    7424:	58001ea5 	ldr	x5, 77f8 <__kvm_hyp_host_forward_smc+0x64>
    7428:	d2800006 	mov	x6, #0x0                   	// #0
    742c:	f2a00006 	movk	x6, #0x0, lsl #16
    7430:	f2c00006 	movk	x6, #0x0, lsl #32
    7434:	f2e00006 	movk	x6, #0x0, lsl #48
    7438:	cb0600a5 	sub	x5, x5, x6
    743c:	d61f00a0 	br	x5
```
We then manually annotate it with constraints as in the following:
```
//@constraint: = (bvand (bvadd SP_EL2 0x0000000000000008) 0xfff0000000000007) 0x0000000000000000
//@constraint: = (bvand (bvsub SP_EL2 0x0000000000000010) 0xfff0000000000007) 0x0000000000000000
    7400:	a9bf07e0 	stp	x0, x1, [sp, #-16]!
    7404:	d53c5200 	mrs	x0, esr_el2
    7408:	d35afc00 	lsr	x0, x0, #26
    740c:	f100581f 	cmp	x0, #0x16
    7410:	54ff9f81 	b.ne	6800 <__host_exit>  // b.any
//@constraint: = (bvand SP_EL2 0xfff0000000000007) 0x0000000000000000
//@constraint: = (bvand (bvadd SP_EL2  0x0000000000000008) 0xfff0000000000007) 0x0000000000000000
    7414:	a94007e0 	ldp	x0, x1, [sp]
    7418:	f1000c1f 	cmp	x0, #0x3
    741c:	54ff9f22 	b.cs	6800 <__host_exit>  // b.hs, b.nlast
    7420:	910043ff 	add	sp, sp, #0x10
//@constraint: = (bvand 0x00000000000077f8 0xfff0000000000007) 0x0000000000000000
    7424:	58001ea5 	ldr	x5, 77f8 <__kvm_hyp_host_forward_smc+0x64>
    7428:	d2800006 	mov	x6, #0x0                   	// #0
    742c:	f2a00006 	movk	x6, #0x0, lsl #16
    7430:	f2c00006 	movk	x6, #0x0, lsl #32
    7434:	f2e00006 	movk	x6, #0x0, lsl #48
    7438:	cb0600a5 	sub	x5, x5, x6
    743c:	d61f00a0 	br	x5
```
and write the result to a file named `pkvm_handler/pkvm_handler.dump`. Note
that lines with a `//@constraint: ...` annotation apply to the next line with
an instruction. Empty lines, comment lines (starting with `//` not immediately
followed by `@`), as well as label lines found in objdump output are ignored.
See file `examples/binary_search.dump` for a more complete example of valid
syntax.

To run the development version of `isla-footprint` (necessary for `islaris`),
we provide a script in `bin/isla-footprint` that must be placed in the `PATH`.
```sh
# Run this command at the root of the repo.
export PATH=$PWD/bin:$PATH
```
We can then run the front end with the following command:
```sh
dune exec -- islaris pkvm_handler/pkvm_handler.dump
```
This will generate one Coq file per address containing the trace for the instruction at
that address and a file called `instrs.v` containing a mapping from addresses to
traces. `instrs.v` may need to be manually modified to correctly qualify imports.

Note that you can also extend the `PATH` directly when calling `islaris`, by
using the following command instead.
```sh
# This assumes you are at the root of the repo.
PATH=$PWD/bin:$PATH dune exec -- islaris pkvm_handler/pkvm_handler.dump
```

## Building other examples

Islaris ships with other examples under directory `examples`.
To build these, run `make generate`. To build an individual example,
consult the Makefile for the correct keyword to use (for instance,
the `unaligned_accesses` example can be built with 
`make generate_unaligned_accesses`).
Building examples with a `make generate_` command will correctly place
the output files under directory `instructions`, in a folder
with the same name as the example.

## People 

- Michael Sammler
- Rodolphe Lepigre
- Angus Hammond
- Brian Campbell
- Jean Pichon-Pharabod
- Peter Sewell
- Derek Dreyer
- Deepak Garg

## LICENSE

2-clause BSD, as in LICENSE, except for THIRD_PARTY_FILES.md

## Funding

This was in part funded from the European Research Council (ERC) under
the European Union’s Horizon 2020 research and innovation programme
(grant agreement No 789108, "ELVER"), in part supported by the UK
Government Industrial Strategy Challenge Fund (ISCF) under the Digital
Security by Design (DSbD) Programme, to deliver a DSbDtech enabled
digital platform (grant 105694), and in part funded by Google.

