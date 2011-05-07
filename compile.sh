#!/bin/sh
set -e
set -x
if false; then
  OCAMLC=ocamlopt
  SUF=cmx
else
  OCAMLC="ocamlc -g"
  SUF=cmo
fi
rm -f parser.ml parser.mli lexer.ml lexer.mli lexer.cm? parser.cm?
$OCAMLC -c expr.ml
menhir --infer parser.mly
$OCAMLC -c parser.mli
$OCAMLC -c parser.ml
ocamllex lexer.mll
$OCAMLC -c lexer.ml
$OCAMLC -c tevsl.ml
$OCAMLC expr.$SUF lexer.$SUF parser.$SUF tevsl.$SUF -o tevsl
