ifdef WINDOWS
EXEEXT = .exe
endif

ifdef NATIVE
# First making sure that these are win32-producing binaries...
OCAMLC = ocamlc
OCAMLOPT = ocamlopt
MENHIR = menhir --ocamlc ocamlopt
else
OCAMLC = ocamlc -g
MENHIR = menhir --infer
endif
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc -v
OCAMLMKTOP = ocamlmktop
OCAMLDEP = ocamldep
OCAMLDSORT = ocamldsort
VERSION = 0.01

COBJ = 

# Source plus generated files.
OCAMLSRC := expr.ml lexer.ml parser.ml tevsl.ml

ifdef NATIVE
OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -opt $(OCAMLSRC))
else
OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -byte $(OCAMLSRC))
endif

TARGET = tevsl$(EXEEXT)

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
	rm -f *.cmo *.cmi *.cmx $(TARGET) parser.ml lexer.ml

cleaner: clean
	rm -f .depend

ML_ERROR:
	@echo Some sort of Ocaml dependency error occurred.
	@false

# core compiler
ifdef NATIVE
$(TARGET): $(OCAMLOBJ)
	$(OCAMLOPT) $(OCAMLOBJ) -o $@
else
$(TARGET): $(OCAMLOBJ)
	$(OCAMLC) $(OCAMLOBJ) -o $@
endif

# Also include (lex, yacc) generated files here.
.depend:	$(OCAMLSRC)
	$(OCAMLDEP) $(OCAMLSRC) > .depend

%.cmo: %.ml
	$(OCAMLC) $< -c -o $@

%.cmx: %.ml
	$(OCAMLOPT) $< -c -o $@

%.cmi: %.mli
	$(OCAMLC) $< -c -o $@

%.ml: %.mly
	$(MENHIR) $<

%.ml: %.mll
	$(OCAMLLEX) $<

# Extra dependencies.
ifdef NATIVE
parser.ml:	expr.cmx
else
parser.ml:	expr.cmo
endif

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),cleaner)
include .depend
endif
endif
