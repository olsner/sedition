N = 2

all: sed runtests README.html

%.html: %.md
	markdown $< >$@

sed: Sed.hs force
	ghc -O2 -j$(N) --make -threaded -rtsopts -o $@ $<

# Compiles after 'sed' because they're sharing modules.
ParserTest: force sed
	ghc -O2 -j$(N) --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

clean:
	rm -f sed Sed Sed.o Sed.hi Parser.o Parser.hi AST.hi AST.o Bus.hi Bus.o
	rm -f ParserTest ParserTest.hi ParserTest.o
	rm -f README.html

.PHONY: force runtests clean
