N = 12

OUTDIR = out
WARNINGS = -Widentities -Wcompat -Wall -Wno-name-shadowing -Wno-missing-signatures
GHCPACKAGES = random regex-base regex-posix trifecta network file-embed
GHCFLAGS = -j$(N) -odir $(OUTDIR) -hidir $(OUTDIR) -O2 -threaded -rtsopts $(WARNINGS) -dynamic $(addprefix -package , $(GHCPACKAGES))
GHC ?= ghc

all: sed run-parsertest README.html

%.html: %.md
	markdown $< >$@

browse-readme: README.html
	xdg-open $<

sed: Sed.hs force
	@mkdir -p $(OUTDIR)
	$(GHC) $(GHCFLAGS) --make -o $@ -main-is Sed $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	@mkdir -p $(OUTDIR)
	$(GHC) $(GHCFLAGS) --make -main-is ParserTest $@

RegexParserTest: force sed
	@mkdir -p $(OUTDIR)
	$(GHC) $(GHCFLAGS) --make -main-is RegexParserTest $@

check: run-parsertest run-bsdtests run-gnused-tests compiler-tests
test: check
compiler-tests: run-bsdtests-compiled run-gnused-tests-compiled

run-parsertest: ParserTest
	./ParserTest

run-regexparsertest: RegexParserTest
	./RegexParserTest

# There are a handful of failing BSD tests still, so ignore failures so we get
# to the other test suites.
run-bsdtests: sed
	cd tests && ./bsd.sh

run-bsdtests-compiled: sed
	cd tests && ./bsd.sh ../runsed

run-gnused-tests: sed
	@if test -d gnused; \
		then \
			echo "Running GNU tests on interpreter..."; \
			./run-gnused-tests.sh gnused; \
		else echo "Check out GNU sed into a directory called gnused"; \
	fi

run-gnused-tests-compiled: sed
	@if test -d gnused; \
		then \
			echo "Running GNU tests on compiler..."; \
			SED=`pwd`/runsed ./run-gnused-tests.sh gnused; \
		else echo "Check out GNU sed into a directory called gnused"; \
	fi

MODULES = Sed Parser AST Bus ParserTest IR \
	Optimize ConstPred RedundantBranches LivePred \
	LiveString SameString Compile Interpret \
	Regex RegexParserTest

clean:
	rm -f sed Sed ParserTest
	rm -f $(MODULES:%=%.o) $(MODULES:%=%.hi)
	rm -f $(MODULES:%=$(OUTDIR)/%.o) $(MODULES:%=$(OUTDIR)/%.hi)
	rm -f README.html

.PHONY: force runtests clean
