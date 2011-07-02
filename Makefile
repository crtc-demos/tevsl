
OCAMLC = ocamlc -g
OCAMLLEX = ocamllex
OCAMLYACC = ocamlyacc -v
OCAMLMKTOP = ocamlmktop
MENHIR = menhir
OCAMLDEP = ocamldep
OCAMLDSORT = ocamldsort

COBJ = 

# Source plus generated files.
OCAMLSRC := expr.ml lexer.ml parser.ml tevsl.ml

OCAMLOBJ := $(shell < .depend $(OCAMLDSORT) -byte $(OCAMLSRC))

TARGET = tevsl

all:	$(TARGET)

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
