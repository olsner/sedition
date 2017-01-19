N = 2

all: Sed runtests

Sed: force
	ghc -O2 -j$(N) --make -threaded -rtsopts $@

ParserTest: force
	ghc -O0 -j$(N) --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

clean:
	rm -f Sed Sed.o Sed.hi Parser.o Parser.hi AST.hi AST.o Bus.hi Bus.o
	rm -f ParserTest ParserTest.hi ParserTest.o

.PHONY: force runtests clean
