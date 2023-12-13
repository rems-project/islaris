#!/bin/bash

# Usage: just enter the new hash bellow, and run the script from the root of
# the repository. Note that the script is self-modifying: it will change the
# old hash into the new one, and erase the new hash again.

OLD_HASH=309be26729b511570e2d31f69c6ba1ce1dc00779
NEW_HASH=

sed -i "s/${OLD_HASH}/${NEW_HASH}/g" README.md .gitlab-ci.yml .github/workflows/ci.yml update_isla_lang.sh Makefile
sed -i "s/^NEW_HASH=.*/NEW_HASH=/g" update_isla_lang.sh

make builddep
