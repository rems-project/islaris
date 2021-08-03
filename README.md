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

# TODOs

- [ ] Figure out how to talk about post condition of some asm code (Michael)
- [ ] Look at exception vectors (Angus / Peter)
  - Looking at the code
    - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kernel/hyp-stub.S
      - trivial, good for starting?!
    - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kvm/hyp/nvhe/hyp-init.S
    - https://github.com/rems-project/linux-pkvm-verif/blob/pkvm/arch/arm64/kvm/hyp/nvhe/host.S
      - more complex than the ones that Wedson looked at
  - Looking at Wedson's thesis
- [ ] Look at traces generated for memory instructions (e.g. str, ldr)
      and try to prove a handwritten spec for a single str / ldr (Angus)
      - as part of this: figure out precondition for "normal" usage
- [ ] Figure out a sensible replacement for the default reset
  - How to do this:
    - Add a new flag to isla to disable the reset (Brian)
    - Play around with different default values for the registers with reset disabled (Angus)
- [X] Add assert instruction to program logic (Rodolphe)
- [ ] More work on bitvectors (Michael)
  - Performance improvements
- [ ] Try stating and proving the receptiveness property for instructions (Michael)
- [ ] Tree-shaped traces (???)
- [X] Write frontend that generates isla traces in Coq (Rodolphe)
- [X] Add memory model and try out memory instructions (Angus)
