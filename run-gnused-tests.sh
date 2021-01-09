#!/bin/bash
# Usage: $0 PATH-TO-GNUSED
# Should be a checkout of the gnu sed repo or unpacked tarball.

usage() {
    echo >&2 "Usage: $0 PATH-TO-GNUSED"
    exit 1
}

addpass() {
    echo "PASS: $1"
    passes=$(( passes+1 ))
}

addfail() {
    echo "FAIL: $1"
    fails=$(( fails+1 ))
}

set -e

test -d "$1" || usage

gnused=$(realpath "$1")
export abs_top_srcdir=$gnused
export abs_top_srcdir=$gnused
export SED=`pwd`/sed

fails=0
passes=0

cd $gnused
test -x "$SED"
# TODO Are there more extensions for sed scripts here?
for t in testsuite/*.sed; do
    name=$(basename -s .sed "$t")
    if testsuite/runtest "$name" &>/dev/null; then
        addpass "$name"
    else
        addfail "$name"
    fi
done

echo PASS: $passes
echo FAIL: $fails
