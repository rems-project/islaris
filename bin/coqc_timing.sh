#!/bin/bash

set -e

# Wrapper for coqc that is used when running the perf script in the CI.
# Variable TIMECMD is expected to contain an absolute path to the perf script.
# If TIMECMD is not set (or empty), fallback to just calling coqc.

if [ -z "${TIMECMD}" ]; then
  coqc "$@"
else
  ${TIMECMD} coqc "$@"
fi
