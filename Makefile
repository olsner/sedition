Sed: force
	ghc -O2 --make -threaded -rtsopts $@

clean:
	rm -f Sed Sed.o Sed.hi Parser.o Parser.hi AST.hi AST.o

.PHONY: force
