N = 12

OUTDIR = dist-newstyle
CABAL ?= cabal

# Default target just runs the parser tests that run fast, do an explicit
# make test to run the BSD and GNU test suites.
all: build cabal-test README.html

%.html: %.md
	markdown $< >$@

sedition.s: sedition.h
	sed 's/^static //' $< | gcc -g -O3 -S -x c - -o $@

generated: sedition.s

browse-readme: README.html
	xdg-open $<

cabal-build: force generated
	$(CABAL) build

cabal-test: cabal-build
	$(CABAL) test

# Create a symlink from the impossible-to-find cabal output directory so the
# test suite can find the sed to run.
sed: cabal-build
	ln -sf `$(CABAL) list-bin sedition:exe:sedition` sed

tdfa2c: cabal-build
	ln -sf `$(CABAL) list-bin sedition:exe:tdfa2c` tdfa2c

check: run-bsdtests run-gnused-tests compiler-tests
test: check
compiler-tests: c-tests asm-tests

c-tests: run-bsdtests-c run-gnused-tests-c
asm-tests: run-bsdtests-asm run-gnused-tests-asm

test: cabal-test
build: cabal-build sed tdfa2c

# There are a handful of failing BSD tests still, so ignore failures so we get
# to the other test suites.
run-bsdtests: sed
	@echo "Running BSD tests on interpreter..."
	cd tests && ./bsd.sh

run-bsdtests-c: sed
	@echo "Running BSD tests on C backend..."
	cd tests && ./bsd.sh ../runsed

run-bsdtests-asm: sed
	@echo "Running BSD tests on assembly backend..."
	cd tests && ./bsd.sh ../runsed-asm

gnused:
	@test -d gnused || echo "Check out GNU sed into a directory called gnused"
	@test -d gnused

run-gnused-tests: sed gnused
	@echo "Running GNU tests on interpreter..."
	./run-gnused-tests.sh gnused

run-gnused-tests-c: sed gnused
	@echo "Running GNU tests on C backend..."
	SED=`pwd`/runsed ./run-gnused-tests.sh gnused

run-gnused-tests-asm: sed gnused
	@echo "Running GNU tests on assembly backend..."
	SED=`pwd`/runsed-asm ./run-gnused-tests.sh gnused

clean:
	$(CABAL) clean --save-config
	rm -f README.html

.PHONY: force runtests clean
