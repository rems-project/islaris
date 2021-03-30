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
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#9f3a825a5f32a8245101a57105a5598a1adf6879"
make builddep
```

You might need to run `eval $(opam env)` afterwards to update the environment of your shell.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

# TODOs

- [ ] Write frontend that generates isla traces in Coq (Rodolphe)
- [ ] Add memory model and try out memory instructions (Angus)
- [ ] More work on bitvectors (Michael)
- [ ] Try stating and proving the receptiveness property for instructions (Michael)
- [ ] Tree-shaped traces (???)
- [ ] Look at exception vectors (currently blocked on other pieces)
