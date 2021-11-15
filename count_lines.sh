#!/bin/bash

set -e
OUTPUT_DIR="/tmp/islaris_lines"

mkdir -p "$OUTPUT_DIR"

for e in "examples/memcpy" "examples/memcpy_riscv64" "examples/binary_search" "examples/binary_search_riscv64" "examples/rbit" "examples/simple_hvc" "examples/uart" "pkvm_handler/wp"; do
    # see https://stackoverflow.com/a/4858011
    sed -n '/(\*SPEC_START\*)/{:a;n;/(\*SPEC_END\*)/b;p;ba}' "$e.v" > "$OUTPUT_DIR/$(basename $e)_spec.txt"
    sed -n '/(\*PROOF_START\*)/{:a;n;/(\*PROOF_END\*)/b;p;ba}' "$e.v" > "$OUTPUT_DIR/$(basename $e)_proof.txt"
done

tokei -f -s files "$OUTPUT_DIR"
