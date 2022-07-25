#!/bin/bash
# Usage: $0 PATH-TO-GNUSED
# Should be a checkout of the gnu sed repo or unpacked tarball.
#
# Note that changes are necessary in the gnu sed repo to e.g. allow us to test
# sedition instead of the sed built inside the gnu sed tree. Should start
# building sedness instead of this...

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
# Allow running this wrapper on any sed, e.g. SED=`which sed` for system sed.
if [ -z "$SED" ]; then
    export SED=`pwd`/sed
fi
# the test script wants file descriptor 9 open to stderr?
exec 9>&2
# "very expensive" is apparently only used for regex-max-int. Not sure if that
# applies to us.
export RUN_VERY_EXPENSIVE_TESTS=yes

good=(
    dc
    madding
    newjis
    range-overlap
    stdin
    xemacs
)
# Failing tests that are bugs in sedition
bad=(
    # Octal escapes in input not implemented
    8bit
    # More octal/decimal/hex escapes stuff. Would be good to sort out :)
    convert-number
    # Print first line not implemented
    binary
    # Index out of range when using s with explicit nth match
    bug32271-1
    # Bad but not for the usual reason. There's no memory buffer size limit in
    # sedition (although POSIX regex C api might have some?) but regex-posix
    # mishandles NULs so the substitution is not done anyway.
    regex-max-int
    # unimplemented: /e flag and in particular the e command
    # unimplemented: -i flag
    eval
    # Handling '-' as file name rather than stdin/out with -i
    in-place-hyphen
    # Something with binary strings in the input.
    mac-mf
    # unimplemented: -i flag
    temp-file-cleanup
)
ugly=(
    # We have our own adaptation of the BSD tests...
    bsd
    # Tests things we don't care about or that are GNU specific or that are
    # intentionally changed/added in sedition.
    cmd-0r
    help-version
    inplace-selinux
    nulldata
    obinary
    # Valgrind tests for bugs.
    bug32082
    bug32271-2
    invalid-mb-seq-UMR
    newline-dfa-bug
    # Eugh. Multibyte encodings. I think we're simply not going to support
    # that. Input is simply 8-bit bytes (or perhaps ISO-8859-1).
    badenc
    mb-bad-delim
    mb-charclass-non-utf8
    mb-match-slash
    mb-y-translate
    subst-mb-incomplete
    # locale dependent
    title-case
    word-delim
    # tests about l/literals, which are formatted differently in sedition and
    # the line width stuff is not implemented.
    8to7
    cmd-l
    # Error handling tests. Errors will look different anyway.
    colon-with-no-label
    missing-filename
    # --follow-symlinks command line flag?
    follow-symlinks-stdin
    # No --posix mode, and no sandbox.
    posix-mode-bad-ref
    posix-mode-N
    sandbox
)

if [ $# -gt 0 ]; then
    tests=( "$@" )
    quiet=
else
    tests=( ${good[@]} )
    quiet="&>/dev/null"
fi

fails=0
passes=0

cd $gnused/testsuite
test -x "$SED"
# TODO Are there more extensions for sed scripts here?
for t in "${tests[@]}"; do
    name=$(basename -s .sh "$t")
    if ! test -x ${name}.sh; then
        echo "${name}: not a test"
        continue
    fi
    if eval "./${name}.sh $quiet"; then
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
