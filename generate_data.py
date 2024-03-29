#!/usr/bin/env python3
import sys
import re
import json
import subprocess
import shutil
import os
import glob

SPEC_START = "(*SPEC_START*)"
SPEC_END = "(*SPEC_END*)"
PROOF_START = "(*PROOF_START*)"
PROOF_END = "(*PROOF_END*)"

# asm is the number of assembly instructions in the corresponding dump file and counted by hand
# isla is the time running isla on the dump file and was generated by adding "time" in front of every call to islaris in the Makefile and then running [make generate]
examples = [
    { "file": "pkvm_handler/wp", "instrs": "pkvm_handler", "asm": 47, "isla": 37},
    { "file": "examples/memcpy", "asm": 8, "isla": 6},
    { "file": "examples/memcpy_riscv64", "asm": 8, "isla": 1},
    { "file": "examples/binary_search", "instrs": "instructions/binary_search", "asm": 32, "isla": 25},
    { "file": "examples/binary_search_riscv64", "instrs": "instructions/binary_search_riscv64", "asm": 48, "isla": 5},
    { "file": "examples/rbit", "asm": 2, "isla": 3},
    { "file": "examples/simple_hvc", "asm": 13, "isla": 10},
    { "file": "examples/uart", "asm": 14, "isla": 10},
    { "file": "examples/unaligned_accesses", "asm": 1, "isla": 2, "add_compute": False},
]
env = {
    **os.environ,
    "TIMECMD": "time -f \\t%es\\t%P",
}
data = []

for e in examples:
    example_data = { "file" : e["file"], "asm": e["asm"], "isla": e["isla"] }
    coq_file = e["file"] + ".v"
    compiled_coq_file = "_build/default/" + e["file"] + ".vo"

    print("Running", coq_file)

    if "add_compute" not in e or e["add_compute"]:
        subprocess.run(
            ["sed", "-i", 's/instrs.$/instrs. Compute (sum_list (isla_trace_length <$> instr_map.*2))./', coq_file],
            check = True)
    if os.path.isfile(compiled_coq_file):
        os.remove(compiled_coq_file)
    output = subprocess.run(
        ["dune", "build", "-j1", compiled_coq_file, "--display", "short"],
        check = True, env=env, stderr=subprocess.PIPE).stderr.decode("utf8")

    # print("Output:", output)
    example_data["itl"] = int(re.search(r"= ([0-9]+)%nat", output).group(1))
    example_data["total"] = float(re.findall(r"^\s*([0-9]+\.[0-9]+)s", output, re.MULTILINE)[-1])
    example_data["lithium"] = sum(map(float, re.findall(r"Tactic call liARun ran for ([0-9]+\.[0-9]+) secs", output)))
    example_data["Qed"] = sum(map(float, re.findall(r"Finished transaction in ([0-9]+\.[0-9]+) secs", output)))
    example_data["other"] = example_data["total"] - example_data["lithium"] - example_data["Qed"]

    with open(coq_file, "r") as f:
        proof = 0
        spec = 0
        is_in_proof = False
        is_in_spec = False
        for line in f:
            line = line.strip()
            if line == "":
                continue
            if line == SPEC_START:
                assert(not is_in_spec and not is_in_proof)
                is_in_spec = True
                continue
            assert(not SPEC_START in line)
            if line == SPEC_END:
                assert(is_in_spec and not is_in_proof)
                is_in_spec = False
                continue
            assert(not SPEC_END in line)
            if line == PROOF_START:
                assert(not is_in_spec and not is_in_proof)
                is_in_proof = True
                continue
            assert(not PROOF_START in line)
            if line == PROOF_END:
                assert(not is_in_spec and is_in_proof)
                is_in_proof = False
                continue
            assert(not PROOF_END in line)
            assert(not (is_in_spec and is_in_proof))
            if is_in_spec:
                spec += 1
                # print("spec:", line)
            if is_in_proof:
                proof += 1
                # print("proof:", line)
        example_data["spec"] = spec
        example_data["proof"] = proof

    print(example_data)
    if "instrs" in e:
        instrs_file = "_build/default/" + e["instrs"] + "/instrs.vo"
        spec_glob = "_build/default/" + e["instrs"] + "/*_spec.vo"
        for filename in glob.glob(spec_glob):
            os.remove(filename)
        output = subprocess.run(
            ["time", "dune", "build", instrs_file, "--display", "short"],
            check = True, stderr=subprocess.PIPE).stderr.decode("utf8")
        example_data["instrs"] = float(re.search(r"0:([0-9]+.[0-9]+)elapsed", output).group(1))

        print(example_data)

    data.append(example_data)

print(json.dumps(data, indent=2))

output_file = 'data.json'
with open(output_file, 'w') as f:
    json.dump(data, f, indent=2)
print("Data written to [" + output_file + "].")
