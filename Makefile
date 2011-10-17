
ifdef WINDOWS
OCAMLC = i686-w64-mingw32-ocamlopt
else
OCAMLC = ocamlc -g
endif
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc -v
OCAMLMKTOP = ocamlmktop
MENHIR = menhir
OCAMLDEP = ocamldep
OCAMLDSORT = ocamldsort
VERSION = 0.01

COBJ = 

# Source plus generated files.
OCAMLSRC := expr.ml lexer.ml parser.ml tevsl.ml

OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -byte $(OCAMLSRC))

TARGET = tevsl

all:	$(TARGET)

.PHONY:	release
release:
	rm -rf tevsl-$(VERSION)
	mkdir tevsl-$(VERSION)
	mkdir tevsl-$(VERSION)/tests
	cp -r $(OCAMLSRC) parser.mly lexer.mll README Makefile \
	      tevsl-$(VERSION)
	cp -r tests/*.tev tevsl-$(VERSION)/tests
	tar fcjv ../tevsl-$(VERSION).tar.bz2 tevsl-$(VERSION)

clean:
	rm -f *.cmo *.cmi $(TARGET) parser.ml lexer.ml

cleaner: clean
	rm -f .depend

ML_ERROR:
	@echo Some sort of Ocaml dependency error occurred.
	@false

# core compiler
$(TARGET): $(OCAMLOBJ)
	$(OCAMLC) $(OCAMLOBJ) -o $@

# Also include (lex, yacc) generated files here.
.depend:	$(OCAMLSRC)
	$(OCAMLDEP) $(OCAMLSRC) > .depend

%.cmo: %.ml
	$(OCAMLC) $< -c -o $@

%.cmi: %.mli
	$(OCAMLC) $< -c -o $@

%.ml: %.mly
	$(MENHIR) --infer $<

%.ml: %.mll
	$(OCAMLLEX) $<

# Extra dependencies.
parser.ml:	expr.cmo

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),cleaner)
include .depend
endif
endif
