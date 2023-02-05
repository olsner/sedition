#!/bin/bash -
#	$OpenBSD: sed.test,v 1.4 2008/10/07 15:02:45 millert Exp $
#
# Copyright (c) 1992 Diomidis Spinellis.
# Copyright (c) 1992, 1993
#	The Regents of the University of California.  All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
# 3. Neither the name of the University nor the names of its contributors
#    may be used to endorse or promote products derived from this software
#    without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
# OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
# HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
# LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
# OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
# SUCH DAMAGE.
#
#	from: @(#)sed.test	8.1 (Berkeley) 6/6/93
#

# sed Regression Tests
#
# The following files are created:
# lines[1-4], script1, script2
# Two directories *.out contain the test results

main()
{
	BASE=`type -p sed`
	BASELOG=sed.out
	TEST=${1-../sed}
	TESTLOG=nsed.out
	DICT=/usr/share/dict/words
    export LC_ALL=C

	test_error | cat

	awk 'END { for (i = 1; i < 15; i++) print "l1_" i}' </dev/null >lines1
	awk 'END { for (i = 1; i < 10; i++) print "l2_" i}' </dev/null >lines2

	test_sedition $TEST

	exec 4>&1 5>&2

	# Set these flags to get messages about known problems
	BSD=0
	GNU=1
	SUN=0
	tests $BASE $BASELOG

	BSD=0
	GNU=1
	SUN=0
	tests $TEST $TESTLOG
	exec 1>&4 2>&5
	diff -c $BASELOG $TESTLOG | diffstat

    # Set exit status to fail when the test fails
    diff -q $BASELOG $TESTLOG >/dev/null
}

tests()
{
	SED=$1
	DIR=$2
	rm -rf $DIR
	mkdir $DIR
	MARK=100

	test_args
	test_addr
	echo Testing commands
	test_group
	test_acid
	test_branch
	test_pattern
	test_print
	test_subst
}

mark()
{
	MARK=`expr $MARK + 1`
	exec 1>&4 2>&5
	exec >"$DIR/${MARK}_$1"
	echo "Test $1:$MARK"
	# Uncomment this line to match tests with sed error messages
	#echo "Test $1:$MARK" >&5
}

test_args()
{
    test -n "$SED" || exit 1
	mark '1.1'
	echo Testing argument parsing
	echo First type
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED 's/^/e1_/p' lines1
	fi
	mark '1.2' ; $SED -n 's/^/e1_/p' lines1
	mark '1.3'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED 's/^/e1_/p' <lines1
	fi
	mark '1.4' ; $SED -n 's/^/e1_/p' <lines1
	echo Second type
	mark '1.4.1'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed fails this
	fi
	$SED -e '' <lines1
	echo 's/^/s1_/p' >script1
	echo 's/^/s2_/p' >script2
	mark '1.5'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -f script1 lines1
	fi
	mark '1.6'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -f script1 <lines1
	fi
	mark '1.7'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -e 's/^/e1_/p' lines1
	fi
	mark '1.8'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -e 's/^/e1_/p' <lines1
	fi
	mark '1.9' ; $SED -n -f script1 lines1
	mark '1.10' ; $SED -n -f script1 <lines1
	mark '1.11' ; $SED -n -e 's/^/e1_/p' lines1
	mark '1.12'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -n -e 's/^/e1_/p' <lines1
	fi
	mark '1.13'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -e 's/^/e1_/p' -e 's/^/e2_/p' lines1
	fi
	mark '1.14'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -f script1 -f script2 lines1
	fi
	mark '1.15'
	if [ $GNU -eq 1 -o $SUN -eq 1 ] ; then
		echo GNU and SunOS sed fail this following older POSIX draft
	else
		$SED -e 's/^/e1_/p' -f script1 lines1
	fi
	mark '1.16'
	if [ $SUN -eq 1 ] ; then
		echo SunOS sed prints only with -n
	else
		$SED -e 's/^/e1_/p' lines1 lines1
	fi
	# POSIX D11.2:11251
	mark '1.17' ; $SED p <lines1 lines1
cat >script1 <<EOF
#n
# A comment

p
EOF
    # TODO sedition doesn't parse #n at start of script
	#mark '1.18' ; $SED -f script1 <lines1 lines1
}

test_addr()
{
	echo Testing address ranges
	mark '2.1' ; $SED -n -e '4p' lines1
	mark '2.2' ; $SED -n -e '20p' lines1 lines2
	mark '2.3' ; $SED -n -e '$p' lines1
	mark '2.4' ; $SED -n -e '$p' lines1 lines2
	mark '2.5' ; $SED -n -e '$a\
hello' /dev/null
	mark '2.6' ; $SED -n -e '$p' lines1 /dev/null lines2
	# Should not print anything
	mark '2.7' ; $SED -n -e '20p' lines1
	mark '2.8' ; $SED -n -e '0p' lines1
	mark '2.9' ; $SED -n '/l1_7/p' lines1
	mark '2.10' ; $SED -n ' /l1_7/ p' lines1
	mark '2.11'
	if [ $BSD -eq 1 ] ; then
		echo BSD sed fails this test
	fi
	if [ $GNU -eq 1 ] ; then
		echo GNU sed fails this
	fi
	$SED -n '\_l1\_7_p' lines1
	mark '2.12' ; $SED -n '1,4p' lines1
	mark '2.13' ; $SED -n '1,$p' lines1 lines2
	mark '2.14' ; $SED -n '1,/l2_9/p' lines1 lines2
	mark '2.15' ; $SED -n '/4/,$p' lines1 lines2
	mark '2.16' ; $SED -n '/4/,20p' lines1 lines2
	mark '2.17' ; $SED -n '/4/,/10/p' lines1 lines2
	mark '2.18' ; $SED -n '/l2_3/,/l1_8/p' lines1 lines2
	mark '2.19'
	if [ $GNU -eq 1 ] ; then
		echo GNU sed fails this
	fi
	$SED -n '12,3p' lines1 lines2
	mark '2.20'
	if [ $GNU -eq 1 ] ; then
		echo GNU sed fails this
	fi
	$SED -n '/l1_7/,3p' lines1 lines2
}

test_group()
{
	echo Brace and other grouping
	mark '3.1' ; $SED -e '
4,12 {
	s/^/^/
	s/$/$/
	s/_/T/
}' lines1
	mark '3.2' ; $SED -e '
4,12 {
	s/^/^/
	/6/,/10/ {
		s/$/$/
		/8/ s/_/T/
	}
}' lines1
	mark '3.3' ; $SED -e '
4,12 !{
	s/^/^/
	/6/,/10/ !{
		s/$/$/
		/8/ !s/_/T/
	}
}' lines1
	mark '3.4' ; $SED -e '4,12!s/^/^/' lines1
}

test_acid()
{
	echo Testing a c d and i commands
	mark '4.1' ; $SED -n -e '
s/^/before_i/p
20i\
inserted
s/^/after_i/p
' lines1 lines2
	mark '4.2' ; $SED -n -e '
5,12s/^/5-12/
s/^/before_a/p
/5-12/a\
appended
s/^/after_a/p
' lines1 lines2
	mark '4.3'
	if [ $GNU -eq 1 ] ; then
		echo GNU sed fails this
	fi
	$SED -n -e '
s/^/^/p
/l1_/a\
appended
8,10N
s/$/$/p
' lines1 lines2
	mark '4.4' ; $SED -n -e '
c\
hello
' lines1
	mark '4.5' ; $SED -n -e '
8c\
hello
' lines1
	mark '4.6' ; $SED -n -e '
3,14c\
hello
' lines1
# SunOS and GNU sed behave differently.   BSD follows POSIX
	mark '4.7' ; $SED -n -e '
8,3c\
hello
' lines1
	mark '4.8' ; $SED d <lines1
	mark '4.9' ; $SED -e '8!chello' lines1
	mark '4.10' ; $SED '
a\
append
2q
' lines1
	mark '4.11' ; $SED -n '
a\
append
2q
' lines1
	mark '4.12' ; $SED '
a\
append
2Q
' lines1
	mark '4.13' ; $SED -n '
a\
append
2Q
' lines1
    # Append and 'n'ext - is it printed before or after the pattern?
	mark '4.14' ; $SED '
a\
append
2n
' lines1
}

test_branch()
{
	mark '5.1' ; $SED -n -e '
b label4
:label3
s/^/label3_/p
b end
:label4
2,12b label1
b label2
:label1
s/^/label1_/p
b
:label2
s/^/label2_/p
b label3
:end
' lines1
	mark '5.2'
	if [ $BSD -eq 1 ] ; then
		echo BSD sed fails this test
	fi
	$SED -n -e '
s/l1_/l2_/
t ok
b
:ok
s/^/tested /p
' lines1 lines2
# SunOS sed behaves differently here.  Clarification needed.
#	mark '5.3' ; $SED -n -e '
#5,8b inside
#1,5 {
#	s/^/^/p
#	:inside
#	s/$/$/p
#}
#' lines1
# Check that t clears the substitution done flag
	mark '5.4' ; $SED -n -e '
1,8s/^/^/
t l1
:l1
t l2
s/$/$/p
b
:l2
s/^/ERROR/
' lines1
# Check that reading a line clears the substitution done flag
	mark '5.5'
	if [ $BSD -eq 1 ] ; then
		echo BSD sed fails this test
	fi
	$SED -n -e '
t l2
1,8s/^/^/p
2,7N
b
:l2
s/^/ERROR/p
' lines1
	mark '5.6' ; $SED 5q lines1
	mark '5.7' ; $SED -e '
5i\
hello
5q' lines1
# Branch across block boundary
	mark '5.8' ; $SED -e '
{
:b
}
s/l/m/
tb' lines1
# Check that reading a line with n/N also clears the substitution done flag
	mark '5.9'
	$SED -n -e '
        s/^/^/p
        /_5/n
        /_7/N
        t l2
        b
        :l2
        s/^/subst-done: /p
    ' lines1
# Check if a conditional substitution clears the substitution done flag
	mark '5.10' ; $SED -e '
s/2$/S/
/_5/! s/_3/_E/
t l1
b
: l1
i label1
b
' lines1
}

test_pattern()
{
# Check that the pattern space is deleted
	mark '6.1' ; $SED -n -e '
c\
changed
p
' lines1
	mark '6.2' ; $SED -n -e '
4d
p
' lines1
# SunOS sed refused to print here
#	mark '6.3' ; $SED -e '
#N
#N
#N
#D
#P
#4p
#' lines1
	mark '6.4' ; $SED -e '
2h
3H
4g
5G
6x
6p
6x
6p
' lines1
	mark '6.5' ; $SED -e '4n' lines1
	mark '6.6' ; $SED -n -e '4n' lines1
}

test_print()
{
	echo Testing print and file routines
	awk 'END {for (i = 32; i < 128; i++) printf("%c", i);print "\n"}' \
		</dev/null >lines3
	# GNU and SunOS sed behave differently here
	mark '7.1' ; $SED -n l lines3
	mark '7.2' ; $SED -e '/l2_/=' lines1 lines2
	rm -f lines4
	mark '7.3' ; $SED -e '3,12w lines4' lines1
	echo w results
	cat lines4
	mark '7.4' ; $SED -e '4r lines2' lines1
    # Seems like /dev/dds is just some device file that doesn't exist.
	mark '7.5' ; $SED -e '5r /dev/dds' lines1
	mark '7.6' ; $SED -e '6r /dev/null' lines1
	mark '7.7'
	if [ $BSD -eq 1 -o $GNU -eq 1 -o $SUN -eq 1 ] ; then
		echo BSD, GNU and SunOS cannot pass this one
	else
		sed '200q' $DICT | sed 's$.*$s/^/&/w tmpdir/&$' >script1
		rm -rf tmpdir
		mkdir tmpdir
		$SED -f script1 lines1
		cat tmpdir/*
		rm -rf tmpdir
	fi
	mark '7.8'
	if [ $BSD -eq 1 ] ; then
		echo BSD sed cannot pass 7.8
	else
		echo line1 > lines3
		echo "" >> lines3
		$SED -n -e '$p' lines3 /dev/null
	fi

	rm -f lines4
	mark '7.9' ; $SED -e '3,12s/.*/&/w lines4' lines1
	echo w results
	cat lines4
}

test_subst()
{
	echo Testing substitution commands
	mark '8.1' ; $SED -e 's/./X/g' lines1
	mark '8.2' ; $SED -e 's,.,X,g' lines1
# GNU and SunOS sed thinks we are escaping . as wildcard, not as separator
#	mark '8.3' ; $SED -e 's.\..X.g' lines1
# POSIX does not say that this should work
#	mark '8.4' ; $SED -e 's/[/]/Q/' lines1
	mark '8.4' ; $SED -e 's/[\/]/Q/' lines1
	mark '8.5' ; $SED -e 's_\__X_' lines1
	mark '8.6' ; $SED -e 's/./(&)/g' lines1
	mark '8.7' ; $SED -e 's/./(\&)/g' lines1
	mark '8.8' ; $SED -e 's/\(.\)\(.\)\(.\)/x\3x\2x\1/g' lines1
	mark '8.9' ; $SED -e 's/_/u0\
u1\
u2/g' lines1
	mark '8.10'
	if [ $BSD -eq 1 ] ; then
		echo 'BSD sed does not understand digit flags on s commands'
	fi
	$SED -e 's/./X/4' lines1
	rm -f lines4
	mark '8.11' ; $SED -e 's/1/X/w lines4' lines1
	echo s wfile results
	cat lines4
	mark '8.12' ; $SED -e 's/[123]/X/g' lines1
	mark '8.13' ; $SED -e 'y/0123456789/9876543210/' lines1
	mark '8.14' ; 
	if [ $BSD -eq 1 -o $GNU -eq 1 -o $SUN -eq 1 ] ; then
		echo BSD/GNU/SUN sed fail this test
	else
		$SED -e 'y10\123456789198765432\101' lines1
	fi
	mark '8.15' ; $SED -e '1N;2y/\n/X/' lines1
	mark '8.16'
	if [ $BSD -eq 1 ] ; then
		echo 'BSD sed does not handle branch defined REs'
	else
		echo 'eeefff' | $SED -e 'p' -e 's/e/X/p' -e ':x' \
		    -e 's//Y/p' -e '/f/bx' | head -100
	fi
	# Check that all 9 back references work.
	mark '8.17' ; echo '123456789' | $SED -e 's/\(.\)\(.\)\(.\)\(.\)\(.\)\(.\)\(.\)\(.\)\(.\)/\9\8\7\6\5\4\3\2\1/g'
	# Actually works fine without setting REG_NOTBOL properly. Seems to be
	# implied when REG_STARTEND is used with a positive offset.
	mark '8.18' ; echo 'aaa' | $SED -e 's/^a/b/g'
	mark '8.19' ; echo | $SED -e 's/a?/b/g'
	mark '8.20' ; echo foo | $SED -e 's/a?/b/g'
	mark '8.21' ; echo foo foo | $SED -e 's/foo$/bar/'
	mark '8.22' ; $SED -e 's/^x*/y/' lines1
	mark '8.23' ; $SED -e 's/^l*/m/' lines1
	mark '8.24' ; $SED -e 's/.*/&/' lines1
    # . should match \n in sed
    mark '8.25' ; $SED -n '1N; s/./f/gp' lines1
    # from dc.sed, regression test(s)
    mark '8.26' ; echo "2002~|P|K0|I10|O10|?~" | $SED -n 's/^[^A-F~]*~.*|I10|/{&}/p'
    #mark '8.27' ; echo "2002~|P|K0|I10|O10|?~" | $SED -n 's/^\(-*\)0*\([0-9.]*[0-9]\)[^~]*/{&}/p'
}

test_sedition()
{
    local SED=$1
    echo Testing sedition-specific features
    # Should provide different random numbers each run!
    if cmp -s <($SED -e '0 g yhjulwwiefzojcbxybbruweejw' /dev/null) <($SED -e '0 g yhjulwwiefzojcbxybbruweejw' /dev/null); then
        echo "FAIL: Same random number twice"
        exit 1
    fi
    # Should provide 32 random characters, plus a newline
    local len=`$SED -e '0 g yhjulwwiefzojcbxybbruweejw' /dev/null | wc -c`
    if [ "$len" -ne 33 ]; then
        echo "FAIL: Should be 32 random characters, got $len"
        exit 1
    fi
}

test_error()
{
	exec 3>&0 4>&1 5>&2
	exec 0</dev/null 1>/dev/null 2>/dev/null
	set -x
	$TEST -x && exit 1
	$TEST -f && exit 1
	$TEST -e && exit 1
	$TEST -f /dev/dds && exit 1
	$TEST p /dev/dds && exit 1
	$TEST -f /bin/sh && exit 1
	$TEST '{' && exit 1
	$TEST '{' && exit 1
	$TEST '/hello/' && exit 1
	$TEST '1,/hello/' && exit 1
	$TEST -e '-5p' && exit 1
	$TEST '/jj' && exit 1
	$TEST 'a hello' && exit 1
	$TEST 'a \ hello' && exit 1
	$TEST 'b foo' && exit 1
	$TEST 'd hello' && exit 1
	$TEST 's/aa' && exit 1
	$TEST 's/aa/' && exit 1
	$TEST 's/a/b' && exit 1
	$TEST 's/a/b/c/d' && exit 1
	$TEST 's/a/b/ 1 2' && exit 1
	$TEST 's/a/b/ 1 g' && exit 1
	$TEST 's/a/b/w' && exit 1
	$TEST 'y/aa' && exit 1
	$TEST 'y/aa/b/' && exit 1
	$TEST 'y/aa/' && exit 1
	$TEST 'y/a/b' && exit 1
	$TEST 'y/a/b/c/d' && exit 1
	$TEST '!' && exit 1
	$TEST supercalifrangolisticexprialidociussupercalifrangolisticexcius
	set +x
	exec 0>&3 1>&4 2>&5
}

main "$@"
