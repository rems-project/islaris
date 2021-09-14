# isla-coq
Isla-lang in Coq

## Setup

It is recommended to install the dependencies of isla-coq via opam
(version 2.0.0 or newer) into a new switch. This can be done via the
following commands:

```
opam switch create . ocaml-base-compiler.4.11.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#7eb94d628845555cb5425f4f4b48890b345efdc5"
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
