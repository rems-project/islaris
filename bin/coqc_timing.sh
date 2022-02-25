#!/bin/bash

set -e

# Wrapper for coqc that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling coqc.
# we need to use opam exec -- coqc to get the coqc installed by opam, not this script

if [ -z "${TIMECMD}" ]; then
  opam exec -- coqc "$@"
else
  ${TIMECMD} opam exec -- coqc "$@"
fi
