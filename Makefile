N = 12

OBJDIR = out
WARNINGS = -Widentities -Wcompat -Wall -Wno-name-shadowing -Wno-missing-signatures
GHCFLAGS = -j$(N) -odir $(OBJDIR) -hidir $(OBJDIR) -O2 -threaded -rtsopts $(WARNINGS)
GHC ?= ghc

all: sed runtests README.html

%.html: %.md
	markdown $< >$@

sed: Sed.hs force
	@mkdir -p $(OBJDIR)
	$(GHC) $(GHCFLAGS) --make -o $@ $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	@mkdir -p $(OBJDIR)
	$(GHC) $(GHCFLAGS) --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

MODULES = Sed Parser AST Bus ParserTest IR \
	Optimize ConstPred RedundantBranches LivePred

clean:
	rm -f sed Sed ParserTest
	rm -f $(MODULES:%=%.o) $(MODULES:%=%.hi)
	rm -f $(MODULES:%=$(OUTDIR)/%.o) $(MODULES:%=$(OUTDIR)/%.hi)
	rm -f README.html

.PHONY: force runtests clean
