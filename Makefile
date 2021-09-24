all:
	@dune build _build/default/coq-isla.install --display short
.PHONY: all

tests:
	@dune runtest
.PHONY: tests

# It is important that tests comes first here as the timing infrastructure breaks otherwise
all_and_tests: tests all
.PHONY: all_and_tests

generate:
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/memory_instructions.dump -o instructions  -n "instr_{instr}" --coqdir=isla.instructions
	rm instructions/instrs.v
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/hello.dump -o instructions/hello --coqdir=isla.instructions.hello
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/example.dump -o instructions/example --coqdir=isla.instructions.example
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/memcpy.dump -o instructions/memcpy --coqdir=isla.instructions.memcpy
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/binary_search.dump -o instructions/binary_search --coqdir=isla.instructions.binary_search
	PATH=$$PWD/bin:$$PATH dune exec -- isla-coq pkvm_handler/pkvm_handler.dump
.PHONY: generate


clean:
	@dune clean
.PHONY: clean

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

builddep-opamfiles: builddep/coq-isla-builddep.opam
	@true
.PHONY: builddep-opamfiles

# Create a virtual Opam package with the same deps as RefinedC, but no
# build. Uses a very ugly hack to use sed for removing the last 4
# lines since head -n -4 does not work on MacOS
# (https://stackoverflow.com/a/24298204)
builddep/coq-isla-builddep.opam: coq-isla.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@sed '$$d' $< | sed '$$d' | sed '$$d' | sed '$$d' | sed -E 's/^name: *"(.*)" */name: "\1-builddep"/' > $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedC are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
builddep: builddep/coq-isla-builddep.opam
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
.PHONY: builddep
