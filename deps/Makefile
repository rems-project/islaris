BBV_COMMIT=d5ab9c04db85eb85688816dc687d118000a65736
SAIL_RISCV_COMMIT=2265a2576fac6d555cfc5f850f78e79c2da56312

all: sail-riscv
.PHONY: all

bbv-%.tar.gz:
	wget "https://github.com/mit-plv/bbv/archive/$*.tar.gz" -O $@

bbv: bbv-$(BBV_COMMIT).tar.gz
	rm -rf bbv
	tar xf bbv-$(BBV_COMMIT).tar.gz
	mv "bbv-${BBV_COMMIT}" bbv
	$(MAKE) -C bbv
	$(MAKE) -C bbv install
.PHONY: bbv

sail-riscv-%.tar.gz:
	wget "https://github.com/riscv/sail-riscv/archive/$*.tar.gz" -O $@

# patch generated via git diff -p -w --ignore-blank-lines . > sail-riscv.patch
sail-riscv-build: bbv sail-riscv-$(SAIL_RISCV_COMMIT).tar.gz
	rm -rf sail-riscv
	tar xf sail-riscv-$(SAIL_RISCV_COMMIT).tar.gz
	mv "sail-riscv-${SAIL_RISCV_COMMIT}/prover_snapshots/coq" sail-riscv
	rm -r "sail-riscv-${SAIL_RISCV_COMMIT}"
	(cd .. && git apply deps/sail-riscv.patch) # Must be applied from the root for paths in the patch to be correct
	sed -i s/omega/lia/ sail-riscv/RV32/riscv_extras.v
	sed -i s/omega/lia/ sail-riscv/RV64/riscv_extras.v
	sed -i s/omega/lia/ sail-riscv/duopod/riscv_extras.v
	chmod a+x sail-riscv/build
	cd sail-riscv && ./build
.PHONY: sail-riscv-build

# This must be a separate goal for the wildcard to be evaluated correctly
sail-riscv: sail-riscv-build
	rm -rf "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/Sail"
	install -m a+rw -D -t "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/Sail" $(wildcard sail-riscv/lib/sail/*.v) $(wildcard sail-riscv/lib/sail/*.vo)
	rm -rf "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RV32"
	install -m a+rw -D -t "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RV32" $(wildcard sail-riscv/RV32/*.v) $(wildcard sail-riscv/RV32/*.vo)
	rm -rf "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RV64"
	install -m a+rw -D -t "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RV64" $(wildcard sail-riscv/RV64/*.v) $(wildcard sail-riscv/RV64/*.vo)
	rm -rf "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RVduopod"
	install -m a+rw -D -t "$(OPAM_SWITCH_PREFIX)/lib/coq/user-contrib/RVduopod" $(wildcard sail-riscv/duopod/*.v) $(wildcard sail-riscv/duopod/*.vo)
.PHONY: sail-riscv

sources: bbv-$(BBV_COMMIT).tar.gz sail-riscv-$(SAIL_RISCV_COMMIT).tar.gz

clean:
	rm -rf *.tar.gz
	rm -rf bbv sail-riscv
.PHONY: clean
