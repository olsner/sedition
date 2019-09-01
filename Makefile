N = 12

OUTDIR = out
WARNINGS = -Widentities -Wcompat -Wall -Wno-name-shadowing -Wno-missing-signatures
GHCFLAGS = -j$(N) -odir $(OUTDIR) -hidir $(OUTDIR) -O2 -threaded -rtsopts $(WARNINGS)
GHC ?= ghc

all: sed runtests README.html

%.html: %.md
	markdown $< >$@

sed: Sed.hs force
	@mkdir -p $(OUTDIR)
# Work around for GHC always compiling the main module into Main.hi/o
	@ln -sf Sed.hi $(OUTDIR)/Main.hi
	@ln -sf Sed.o  $(OUTDIR)/Main.o
	$(GHC) $(GHCFLAGS) --make -o $@ $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	@mkdir -p $(OUTDIR)
	@ln -sf ParserTest.hi $(OUTDIR)/Main.hi
	@ln -sf ParserTest.o  $(OUTDIR)/Main.o
	$(GHC) $(GHCFLAGS) --make $@

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
