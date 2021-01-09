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
shift

export abs_top_srcdir=$gnused
export srcdir=$gnused
export SED=`pwd`/sed

if [ $# -gt 0 ]; then
    tests=( "$@" )
    quiet=
else
    tests=( $gnused/testsuite/*.sed )
    quiet="&>/dev/null"
fi

fails=0
passes=0

cd $gnused/testsuite
test -x "$SED"
# TODO Are there more extensions for sed scripts here?
for t in "${tests[@]}"; do
    name=$(basename -s .sed "$t")
    if eval './runtest "$name" '$quiet; then
        addpass "$name"
    else
        addfail "$name"
        if [ -n "$verbose" -o ${#tests[@]} -eq 1 ]; then
            diff -u $name.good $name.out || true
        fi
    fi
done

echo PASS: $passes
echo FAIL: $fails
