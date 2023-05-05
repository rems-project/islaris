#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=4ee3daa3a9f04b2d6a55dd94026ff5f9d79db5fc
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md .gitlab-ci.yml .github/workflows/ci.yml update_isla_lang.sh Makefile
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_isla_lang.sh

make builddep
