N = 12

OUTDIR = dist-newstyle
CABAL ?= cabal

# Default target just runs the parser tests that run fast, do an explicit
# make test to run the BSD and GNU test suites.
all: build cabal-test README.html

%.html: %.md
	markdown $< >$@

browse-readme: README.html
	xdg-open $<

cabal-build: force
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
compiler-tests: run-bsdtests-compiled run-gnused-tests-compiled

test: cabal-test
build: cabal-build sed tdfa2c

# There are a handful of failing BSD tests still, so ignore failures so we get
# to the other test suites.
run-bsdtests: sed
	@echo "Running BSD tests on interpreter..."
	cd tests && ./bsd.sh

run-bsdtests-compiled: sed
	@echo "Running BSD tests on compiler..."
	cd tests && ./bsd.sh ../runsed

gnused:
	@test -d gnused || echo "Check out GNU sed into a directory called gnused"
	@test -d gnused

run-gnused-tests: sed gnused
	@echo "Running GNU tests on interpreter..."
	./run-gnused-tests.sh gnused

run-gnused-tests-compiled: sed gnused
	@echo "Running GNU tests on compiler..."
	SED=`pwd`/runsed ./run-gnused-tests.sh gnused

clean:
	$(CABAL) clean --save-config
	rm -f README.html

.PHONY: force runtests clean
