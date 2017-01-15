all: Sed runtests

Sed ParserTest: force
	ghc -O2 --make -threaded -rtsopts $@

runtests: ParserTest
	./ParserTest

clean:
	rm -f Sed Sed.o Sed.hi Parser.o Parser.hi AST.hi AST.o

.PHONY: force runtests clean
