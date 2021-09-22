# isla-coq
Isla-lang in Coq

## Setup

It is recommended to install the dependencies of isla-coq via opam
(version 2.0.0 or newer) into a new switch. This can be done via the
following commands:

```
opam switch create . ocaml-base-compiler.4.11.1 --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#7eb94d628845555cb5425f4f4b48890b345efdc5"
opam pin add -n -y isla-lang "git+https://git@github.com/rems-project/isla-lang.git#130ed635dc7f09ad8ba8a30226908925e4ebd6dd"
make builddep
```

You might need to run `eval $(opam env)` afterwards to update the environment of your shell.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

## Generating traces

To regenerate the traces used in the examples, run `./generate_traces.py`.
It expects a script `run_isla_footprint.sh` in the root of this repository that runs `isla-footprint`.
An example for `run_isla_footprint.sh` is:
```bash
#!/bin/bash

set -e
cd ../isla
LD_LIBRARY_PATH=. cargo run --release --bin isla-footprint -- "$@"
```

## Generating Coq traces from a partial decompilation

Currently, one needs to manually instrument the outout of `objdump` so that it
contains only the relevant code, add colons separating the columns, and insert
a third column which contains an isla expression describing any pointers that
isla should assume are well behaved.

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
We then manually transform it into the following:
```
    7400:	a9bf07e0: (= (bvand (bvadd SP_EL2 0x0000000000000008) 0xfff0000000000007) 0x0000000000000000) ; (= (bvand (bvsub SP_EL2 0x0000000000000010) 0xfff0000000000007) 0x0000000000000000)	:stp	x0, x1, [sp, #-16]!
    7404:	d53c5200: 	:mrs	x0, esr_el2
    7408:	d35afc00: 	:lsr	x0, x0, #26
    740c:	f100581f: 	:cmp	x0, #0x16
    7410:	54ff9f81: 	:b.ne	6800 <__host_exit>  // b.any
    7414:	a94007e0: (= (bvand SP_EL2 0xfff0000000000007) 0x0000000000000000) ; (= (bvand (bvadd SP_EL2  0x0000000000000008) 0xfff0000000000007) 0x0000000000000000)	:ldp	x0, x1, [sp]
    7418:	f1000c1f: 	:cmp	x0, #0x3
    741c:	54ff9f22: 	:b.cs	6800 <__host_exit>  // b.hs, b.nlast
    7420:	910043ff: 	:add	sp, sp, #0x10
    7424:	58001ea5: (= (bvand 0x00000000000077f8 0xfff0000000000007) 0x0000000000000000) 	:ldr	x5, 77f8 <__kvm_hyp_host_forward_smc+0x64>
    7428:	d2800006: 	:mov	x6, #0x0                   	// #0
    742c:	f2a00006: 	:movk	x6, #0x0, lsl #16
    7430:	f2c00006: 	:movk	x6, #0x0, lsl #32
    7434:	f2e00006: 	:movk	x6, #0x0, lsl #48
    7438:	cb0600a5: 	:sub	x5, x5, x6
    743c:	d61f00a0: 	:br	x5
```
and write the result to a file named `pkvm_handler/pkvm_handler.dump`. Note
that a `:` is added after the op-code, followed by an optional list of
constraints (separated by `;`), and an additional `:` before the instruction.

To run the development version of `isla-footprint` (necessary for `isla-coq`),
we provide a script in `bin/isla-footprint` that must be placed in the `PATH`.
```sh
# Run this command at the root of the repo.
export PATH=$PWD/bin:$PATH
```
We can then run the front end with the following command:
```sh
dune exec -- isla-coq pkvm_handler/pkvm_handler.dump
```
This will generate one coq file per address containing the trace for the instruction at
that address and a file called `instrs.v` containing a mapping from addresses to
traces. `instrs.v` may need to be manually modified to correctly qualify imports.

Note that you can also extend the `PATH` directly when calling `isla-coq`, by
using the following command instead.
```sh
# This assumes you are at the root of the repo.
PATH=$PWD/bin:$PATH dune exec -- isla-coq pkvm_handler/pkvm_handler.dump
```

# TODOs

- Evaluation
  - [ ] Look at exception vectors (Angus / Peter)
    - Looking at the code
      - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kernel/hyp-stub.S
        - trivial, good for starting?!
      - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kvm/hyp/nvhe/hyp-init.S
      - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kvm/hyp/nvhe/host.S
        - more complex than the ones that Wedson looked at
    - Looking at Wedson's thesis
  - [ ] Verify code that traps to pKVM and then pKVM returns to the code
  - [ ] C algorithmic code (Michael)
    - goal: Reasoning about straightforward code stays feasible even
      though we use the realistic model (but probably not as nice as
      specialized C verification tools)
      - binary search
      - linked list
- [ ] Figure out right register values (Angus)
  - by looking at pKVM running in qEMU
  - running it up to a point where it turned of the MMU
- [ ] Extend traces such that we prove the preconditions passed to isla (Brian)
- [ ] Tree-shaped traces (Brian)
- [ ] Compare isla generated traces against the Sail Coq model (Michael)

Old:

- [X] Look at traces generated for memory instructions (e.g. str, ldr)
      and try to prove a handwritten spec for a single str / ldr (Angus)
      - as part of this: figure out precondition for "normal" usage
- [X] Figure out a sensible replacement for the default reset
  - How to do this:
    - Add a new flag to isla to disable the reset (Brian)
    - Play around with different default values for the registers with reset disabled (Angus)
- [X] Add assert instruction to program logic (Rodolphe)
- [X] More work on bitvectors (Michael)
  - Performance improvements
- [ ] Try stating and proving the receptiveness property for instructions (Michael)
- [X] Figure out how to talk about post condition of some asm code (Michael)
- [X] Write frontend that generates isla traces in Coq (Rodolphe)
- [X] Add memory model and try out memory instructions (Angus)
