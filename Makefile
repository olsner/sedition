N = 12

OUTDIR = out
WARNINGS = -Widentities -Wcompat -Wall -Wno-name-shadowing -Wno-missing-signatures
GHCFLAGS = -j$(N) -odir $(OUTDIR) -hidir $(OUTDIR) -O2 -threaded -rtsopts $(WARNINGS)
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

check: run-parsertest run-bsdtests run-gnused-tests

run-parsertest: ParserTest
	./ParserTest

run-bsdtests: sed
	cd tests && ./bsd.sh

run-gnused-tests: sed
	@if test -d gnused; \
		then ./run-gnused-tests.sh gnused; \
		else echo "Check out GNU sed into a directory called gnused"; \
	fi

MODULES = Sed Parser AST Bus ParserTest IR \
	Optimize ConstPred RedundantBranches LivePred \
	LiveString SameString

clean:
	rm -f sed Sed ParserTest
	rm -f $(MODULES:%=%.o) $(MODULES:%=%.hi)
	rm -f $(MODULES:%=$(OUTDIR)/%.o) $(MODULES:%=$(OUTDIR)/%.hi)
	rm -f README.html

.PHONY: force runtests clean
