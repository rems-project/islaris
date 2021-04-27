#!/bin/bash

echo "; Generated by the Makefile."

for ISLA in "$@"
do
  BASE="$(basename "$ISLA" .isla)"
  cat <<EOM

(rule
 (target $BASE.v)
 (deps $BASE.isla)
 (action (run isla-coq -o %{target} %{deps})))

(rule
 (alias runtest)
 (action (diff $BASE.v $BASE.v.expected)))
EOM
done

unset ISLA BASE
