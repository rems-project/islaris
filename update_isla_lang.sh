#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=14541f64fc25f98ce77be070d1fa3a8eb08207dc
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md .gitlab-ci.yml .github/workflows/ci.yml update_isla_lang.sh
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_isla_lang.sh

opam pin remove -y isla-lang
opam pin add -n -y isla-lang "git+https://github.com/rems-project/isla-lang.git#${NEW_HASH}"
