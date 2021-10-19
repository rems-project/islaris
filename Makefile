all:
	@dune build _build/default/coq-isla.install --display short
.PHONY: all

tests:
	@dune runtest
.PHONY: tests

# It is important that tests comes first here as the timing infrastructure breaks otherwise
all_and_tests: tests all
.PHONY: all_and_tests

ci: restore_dune_project all_and_tests
	@true
.PHONY: ci

generate_aarch64:
	@echo "[isla-coq] examples/memory_instructions.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/memory_instructions.dump -j 8 -o instructions  -n "instr_{instr}" --coqdir=isla.instructions
	@rm instructions/instrs.v
	@echo "[isla-coq] examples/hello.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/hello.dump -j 8 -o instructions/hello --coqdir=isla.instructions.hello
	@echo "[isla-coq] examples/example.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/example.dump -j 8 -o instructions/example --coqdir=isla.instructions.example
	@echo "[isla-coq] examples/memcpy.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/memcpy.dump -j 8 -o instructions/memcpy --coqdir=isla.instructions.memcpy
	@echo "[isla-coq] examples/binary_search.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/binary_search.dump -j 8 -o instructions/binary_search --coqdir=isla.instructions.binary_search
	@echo "[isla-coq] examples/uart.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/uart.dump -j 8 -o instructions/uart --coqdir=isla.instructions.uart
	@echo "[isla-coq] pkvm_handler/pkvm_handler.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq -j 8 pkvm_handler/pkvm_handler.dump
.PHONY: generate_aarch64

generate_riscv64:
	@echo "[isla-coq] examples/riscv64_test.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- isla-coq examples/riscv64_test.dump -j 8 -o instructions/riscv64_test --coqdir=isla.instructions.riscv64_test --arch=riscv64
.PHONY: generate_riscv64

generate: generate_aarch64 generate_riscv64
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
	@echo "# Renaming dune-project to work around coq#15044"
	@mv dune-project dune-project.tmp
	@true
.PHONY: builddep-opamfiles

restore_dune_project:
	@if [ -f dune-project.tmp ] && ! [ -e dune-project ]; then \
		echo "# Renaming dune-project back";\
		mv dune-project.tmp dune-project;\
	fi
.PHONY: restore_dune_project

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
	@echo "# Renaming dune-project to work around coq#15044"
	@mv dune-project dune-project.tmp
	@echo "# Installing package $^."
	@opam install $(OPAMFLAGS) $^
	@echo "# Renaming dune-project back"
	@mv dune-project.tmp dune-project
.PHONY: builddep
