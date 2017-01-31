N = 2

all: sed runtests README.html

%.html: %.md
	markdown $< >$@

sed: Sed.hs force
	ghc -O2 -j$(N) -Wincomplete-patterns --make -threaded -rtsopts -o $@ $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	ghc -O2 -j$(N) -Wincomplete-patterns --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

MODULES = Sed Parser AST Bus ParserTest Optimize ConstPred IR

clean:
	rm -f sed Sed ParserTest
	rm -f $(MODULES:%=%.o) $(MODULES:%=%.hi)
	rm -f README.html

.PHONY: force runtests clean
