SAIL_COMMIT=605cd3cffe4b18fb5d0a99beef5d6ee33e1a7dcb

all: sail-riscv-coq
.PHONY: all

sail-%.tar.gz:
	wget "https://github.com/rems-project/sail/archive/$*.tar.gz" -O $@

# TODO: maybe add opam install z3?
sail: sail-$(SAIL_COMMIT).tar.gz
	rm -rf sail
	tar xf sail-$(SAIL_COMMIT).tar.gz
	mv "sail-${SAIL_COMMIT}" sail
	opam pin add ./sail -n
	sed -i 's#make "-C" "lib/coq"#make "-C" "."#g' ./sail/lib/coq/coq-sail.opam
	opam pin add coq-sail ./sail/lib/coq -n
.PHONY: sail-build

sail-riscv-coq: sail
	opam pin add coq-sail-riscv 'git+https://github.com/bacam/sail-riscv#4f1704c74020e021f2e700b9451f8ddfd230ca62' -n
	opam install coq-sail-riscv
.PHONY: sail-riscv-coq

clean:
	rm -rf *.tar.gz
	rm -rf sail
.PHONY: clean
