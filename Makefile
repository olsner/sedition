N = 2

WARNINGS = -Widentities -Wcompat -Wall -Wno-name-shadowing -Wno-missing-signatures
GHCFLAGS = -j$(N) -O2 -threaded -rtsopts $(WARNINGS)

all: sed runtests README.html

%.html: %.md
	markdown $< >$@

sed: Sed.hs force
	ghc $(GHCFLAGS) --make -o $@ $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	ghc $(GHCFLAGS) --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

MODULES = Sed Parser AST Bus ParserTest IR \
	Optimize ConstPred RedundantBranches LivePred

clean:
	rm -f sed Sed ParserTest
	rm -f $(MODULES:%=%.o) $(MODULES:%=%.hi)
	rm -f README.html

.PHONY: force runtests clean
