#!/bin/sh

set -e

export TIMECMD="time -f \t%es\t%P"

for e in "examples/memcpy" "examples/memcpy_riscv64" "examples/binary_search" "examples/binary_search_riscv64" "examples/rbit" "examples/simple_hvc" "examples/uart" "pkvm_handler/wp"; do
    sed -i 's/instrs.$/instrs. Compute (sum_list (isla_trace_length <$> instr_map.*2))./' "$e.v"
    rm -f "_build/default/$e.vo"
    dune build -j1 "_build/default/$e.vo" --display short
done

for e in "instructions/binary_search" "instructions/binary_search_riscv64" "pkvm_handler"; do
    echo "$e"
    for spec in $e/*_spec.v; do
        rm -f "_build/default/${spec}o"
    done
    time dune build "_build/default/$e/instrs.vo" --display short
done
