
all: qsitory_main.ml syntax.ml evaluation.ml interactive.ml readfile.ml pprint.ml tools.ml lexer.mll parser.mly
	ocamlopt -c tools.ml syntax.ml evaluation.ml pprint.ml
	ocamllex lexer.mll
	menhir --infer --explain parser.mly
	ocamlopt -c parser.mli
	ocamlopt -c lexer.ml
	ocamlopt -c parser.ml
	ocamlopt -o qsitory tools.cmx syntax.cmx evaluation.cmx pprint.cmx parser.cmx lexer.cmx interactive.ml readfile.ml qsitory_main.ml

clean:
	rm -f *.cmi *.cmx *.o
