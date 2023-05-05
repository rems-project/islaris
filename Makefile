all:
	@dune build _build/default/islaris.install --display short
.PHONY: all

tests:
	@dune runtest
.PHONY: tests

# It is important that tests comes first here as the timing infrastructure breaks otherwise
all_and_tests: tests all
.PHONY: all_and_tests

update_etc:
	@dune build _build/install/default/etc/islaris/aarch64_isla_coq.toml
	@dune build _build/install/default/etc/islaris/aarch64_isla_coq_el1.toml
	@dune build _build/install/default/etc/islaris/aarch64_isla_coq_pkvm.toml
	@dune build _build/install/default/etc/islaris/riscv64_isla_coq.toml
.PHONY: update_etc

generate_memory_instructions: examples/memory_instructions.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions  -n "instr_{instr}" --coqdir=isla.instructions
	@rm instructions/instrs.v
.PHONY: generate_memory_instructions

generate_unaligned_accesses: examples/unaligned_accesses.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions  -n "instr_{instr}_unaligned" --coqdir=isla.instructions
	@rm instructions/instrs.v
.PHONY: generate_unaligned_accesses

generate_aarch64: update_etc
	@echo "[islaris] examples/hello.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/hello.dump -j 8 -o instructions/hello --coqdir=isla.instructions.hello
	@echo "[islaris] examples/example.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/example.dump -j 8 -o instructions/example --coqdir=isla.instructions.example
	@echo "[islaris] examples/memcpy.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/memcpy.dump -j 8 -o instructions/memcpy --coqdir=isla.instructions.memcpy
	@echo "[islaris] examples/binary_search.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/binary_search.dump -j 8 -o instructions/binary_search --coqdir=isla.instructions.binary_search
	@echo "[islaris] examples/uart.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/uart.dump -j 8 -o instructions/uart --coqdir=isla.instructions.uart
	@echo "[islaris] pkvm_handler/pkvm_handler.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris -j 8 pkvm_handler/pkvm_handler.dump
.PHONY: generate_aarch64

generate_riscv64: update_etc
	@echo "[islaris] examples/riscv64_test.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/riscv64_test.dump -j 8 -o instructions/riscv64_test --coqdir=isla.instructions.riscv64_test --arch=riscv64
	@echo "[islaris] examples/memcpy_riscv64.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/memcpy_riscv64.dump -j 8 -o instructions/memcpy_riscv64 --coqdir=isla.instructions.memcpy_riscv64 --arch=riscv64
	@echo "[islaris] examples/binary_search_riscv64.dump"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris examples/binary_search_riscv64.dump -j 8 -o instructions/binary_search_riscv64 --coqdir=isla.instructions.binary_search_riscv64 --arch=riscv64
.PHONY: generate_riscv64

generate_el2_to_el1: examples/el2_to_el1.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions/el2_to_el1 --coqdir=isla.instructions.el2_to_el1
.PHONY: generate_el2_to_el1

generate_clz: examples/clz.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions/clz --coqdir=isla.instructions.clz
.PHONY: generate_clz

generate_simple_hvc: examples/simple_hvc.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions/simple_hvc --coqdir=isla.instructions.simple_hvc
.PHONY: generate_simple_hvc

generate_rbit: examples/rbit.dump update_etc
	@echo "[islaris] $<"
	@PATH=$$PWD/bin:$$PATH dune exec -- islaris $< -j 8 -o instructions/rbit --coqdir=isla.instructions.rbit
.PHONY: generate_clz

generate: generate_memory_instructions generate_unaligned_accesses generate_aarch64 generate_riscv64 generate_el2_to_el1 generate_clz generate_simple_hvc generate_rbit
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

SRC = $(wildcard frontend/*.ml) \
			$(wildcard theories/*.v) $(wildcard theories/*/*.v) \
			$(wildcard examples/*.v) pkvm_handler/wp.v \
			$(wildcard sail/*.v) $(wildcard sail-riscv/*.v)
update_license:
	@ocaml tools/update_license.ml LICENSE ${SRC}
.PHONY: update_license

strip_license:
	@ocaml tools/update_license.ml --strip ${SRC}
.PHONY: strip_license

# We cannot use builddep-pins as a dependency of builddep-opamfiles because the CI removes all pins.
builddep-pins:
	@opam pin add -n -y isla-lang "git+https://git@github.com/rems-project/isla-lang.git#14541f64fc25f98ce77be070d1fa3a8eb08207dc"
.PHONY: builddep-pins

builddep-opamfiles: builddep/islaris-builddep.opam
	@true
.PHONY: builddep-opamfiles

# Create a virtual Opam package with the same deps as Islaris, but no
# build. Uses a very ugly hack to use sed for removing the last 4
# lines since head -n -4 does not work on MacOS
# (https://stackoverflow.com/a/24298204)
builddep/islaris-builddep.opam: islaris.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@sed '$$d' $< | sed '$$d' | sed '$$d' | sed '$$d' | sed -E 's/^name: *"(.*)" */name: "\1-builddep"/' > $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of Islaris are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the Islaris package itself (which takes time).
# Note: We also need to install isla-lang to make sure that new pins are propagated correctly.
builddep: builddep/islaris-builddep.opam builddep-pins
	@echo "# Installing package $<."
	@opam install $(OPAMFLAGS) $< isla-lang
.PHONY: builddep

saildep:
	$(MAKE) -C deps
.PHONY: saildep

enable-sail-riscv:
	ln -fs _dune sail-riscv/dune
.PHONY: enable-sail-riscv
